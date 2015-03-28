/*
 * DICOM demuxer
 * Copyright (c) 2015  Mathieu Malaterre
 *
 * This file is part of Libav.
 *
 * Libav is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * Libav is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Libav; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include "libavutil/intreadwrite.h"
#include "libavutil/avassert.h"
#include "avformat.h"
#include "internal.h"

/* voir smush pour exemple */

#include <stdlib.h>

typedef struct DICMContext {
    int video_stream_index;
} DICMContext;

typedef uint32_t tag_t;
typedef uint16_t vr_t;
typedef uint32_t vl_t;

typedef union { uint16_t tags[2]; tag_t tag; } utag_t;
typedef union { char str[2]; vr_t vr; } uvr_t;
typedef union { char bytes[4]; vl_t vl; } uvl_t;
typedef union { char bytes[2]; uint16_t vl16; } uvl16_t;

static inline uint16_t get_group( tag_t tag )
{
  return (uint16_t)(tag >> 16);
}
static inline uint16_t get_element( tag_t tag )
{
  return (uint16_t)(tag & (uint16_t)0xffff);
}

#define MAKE_TAG(group,element) (group << 16 | element)

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define SWAP_TAG(t) t.tag = MAKE_TAG(t.tags[0], t.tags[1])
#else
#define SWAP_TAG(t) t.tags[0] = bswap_16( t.tags[0] ); t.tags[1] = bswap_16( t.tags[1] )
#endif

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define MAKE_VR(left,right) (right << 8 | left)
#else
#define MAKE_VR(left,right) (left << 8 | right)
#endif

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define SWAP_VL(vl)
#define SWAP_VL16(vl)
#else
#define SWAP_VL(vl) vl = bswap_32(vl)
#define SWAP_VL16(vl) vl = bswap_16(vl)
#endif

enum {
  E_INVALID = 0, /* Item, Item Delimitation Item & Sequence Delimitation Item */
  E_AE = MAKE_VR('A','E'),
  E_AS = MAKE_VR('A','S'),
  E_AT = MAKE_VR('A','T'),
  E_CS = MAKE_VR('C','S'),
  E_DA = MAKE_VR('D','A'),
  E_DS = MAKE_VR('D','S'),
  E_DT = MAKE_VR('D','T'),
  E_FL = MAKE_VR('F','L'),
  E_FD = MAKE_VR('F','D'),
  E_IS = MAKE_VR('I','S'),
  E_LO = MAKE_VR('L','O'),
  E_LT = MAKE_VR('L','T'),
  E_OB = MAKE_VR('O','B'),
  E_OD = MAKE_VR('O','D'),
  E_OF = MAKE_VR('O','F'),
  E_OW = MAKE_VR('O','W'),
  E_PN = MAKE_VR('P','N'),
  E_SH = MAKE_VR('S','H'),
  E_SL = MAKE_VR('S','L'),
  E_SQ = MAKE_VR('S','Q'),
  E_SS = MAKE_VR('S','S'),
  E_ST = MAKE_VR('S','T'),
  E_TM = MAKE_VR('T','M'),
  E_UI = MAKE_VR('U','I'),
  E_UL = MAKE_VR('U','L'),
  E_UN = MAKE_VR('U','N'),
  E_US = MAKE_VR('U','S'),
  E_UT = MAKE_VR('U','T'),
};

static inline int isvr_valid( const uvr_t uvr )
{
  if( uvr.str[0] < 'A' || uvr.str[0] > 'Z' ) return 0;
  if( uvr.str[1] < 'A' || uvr.str[1] > 'Z' ) return 0;
  return 1;
}

static inline int isvr32( const vr_t vr )
{
  switch( vr )
    {
  case E_AE:
  case E_AS:
  case E_AT:
  case E_CS:
  case E_DA:
  case E_DS:
  case E_DT:
  case E_FD:
  case E_FL:
  case E_IS:
  case E_LO:
  case E_LT:
  case E_PN:
  case E_SH:
  case E_SL:
  case E_SS:
  case E_ST:
  case E_TM:
  case E_UI:
  case E_UL:
  case E_US:
    /* 16bits: */
    return 0;
  case E_OB:
  case E_OD:
  case E_OF:
  case E_OW:
  case E_SQ:
  case E_UN:
  case E_UT:
    /* 32bits: */
    return 1;
  default:
    /* parser error, or newer DICOM standard */
    /* return 32bits by default (required) */
    return 1;
    }
}

typedef struct
{
  tag_t tag;
  vr_t vr;
  vl_t vl;
} data_element;

static inline int tag_equal_to( const data_element * de, tag_t tag )
{
  return de->tag == tag;
}

static inline int tag_is_lower( const data_element * de, tag_t tag )
{
  return de->tag < tag;
}

static inline int is_start( const data_element * de )
{
  static const tag_t start = MAKE_TAG( 0xfffe,0xe000 );
  const int b = de->tag == start;
  // can be undefined or defined length
  return b;
}
static inline int is_end_item( const data_element * de )
{
  static const tag_t end_item = MAKE_TAG( 0xfffe,0xe00d );
  const int b = de->tag == end_item;
  if( b ) av_assert0( de->vl == 0 );
  return b;
}
static inline int is_end_sq( const data_element * de )
{
  static const tag_t end_sq = MAKE_TAG( 0xfffe,0xe0dd );
  const int b = de->tag == end_sq;
  if( b ) av_assert0( de->vl == 0 );
  return b;
}
static inline int is_encapsulated_pixel_data( const data_element * de )
{
  static const tag_t pixel_data = MAKE_TAG( 0x7fe0,0x0010 );
  const int is_pixel_data = tag_equal_to(de, pixel_data);
  if( is_pixel_data )
    {
    av_assert0( de->vl == (uint32_t)-1 );
    av_assert0( de->vr == E_OB || de->vr == E_OW );
    return 1;
    }
  return 0;
}
static inline int is_undef_len( const data_element * de )
{
  const int b = de->vl == (uint32_t)-1;
  if( b ) av_assert0( de->vr == E_SQ || is_encapsulated_pixel_data( de ) || is_start(de) );
  return b;
}
static inline uint32_t compute_len( const data_element * de )
{
  av_assert0( !is_undef_len( de ) );
  if( isvr32( de->vr ) )
    {
    return 4 /* tag */ + 4 /* VR */ + 4 /* VL */ + de->vl /* VL */;
    }
  return 4 /* tag */ + 4 /* VR/VL */ + de->vl /* VL */;
}
static inline uint32_t compute_undef_len( const data_element * de, uint32_t len )
{
  av_assert0( is_undef_len( de ) );
  av_assert0( len != (uint32_t)-1 );
  return 4 /* tag */ + 4 /* VR */ + 4 /* VL */ + len;
}


static int read_preamble( AVIOContext *pb )
{
  char buf[4];
  int ret;
  avio_skip(pb, 128);
  ret = avio_read(pb, buf, 4);
  if( ret <= 0 ) return AVERROR(EIO);
  if( strncmp( buf, "DICM", 4 ) != 0 ) return AVERROR_INVALIDDATA;
  return 0;
}

// explicit
static int read_explicit( AVIOContext *pb, data_element * de )
{
  utag_t t;
  uvr_t vr;
  uvl_t vl;
  uvl16_t vl16;
  int ret;

  // Tag
  ret = avio_read(pb, (unsigned char*)t.tags, sizeof *t.tags * 2 );
  if( ret <= 0 ) return AVERROR(EIO);
  SWAP_TAG(t);
  av_assert0( tag_is_lower( de, t.tag ) );

  // Value Representation
  ret = avio_read(pb, vr.str, sizeof *vr.str * 2);
  if( ret <= 0 ) return AVERROR(EIO);
  /* a lot of VR are not valid (eg: non-ASCII), however the standard may add
   * them in a future edition, so only exclude the impossible ones
   */
  if( !isvr_valid(vr) )
    {
    av_assert0( 0 );
    return AVERROR_INVALIDDATA;
    }

  // padding and/or 16bits VL
  ret = avio_read( pb, vl16.bytes, sizeof *vl16.bytes * 2);
  if( ret <= 0 ) return AVERROR(EIO);

  // Value Length
  if( isvr32( vr.vr ) )
    {
    /* padding must be set to zero */
    if( vl16.vl16 != 0 ) return AVERROR_INVALIDDATA;

    ret = avio_read(pb, vl.bytes, 4);
    if( ret <= 0 ) return AVERROR(EIO);
    SWAP_VL(vl.vl);
    }
  else
    {
    SWAP_VL16(vl16.vl16);
    vl.vl = vl16.vl16;
    }
  de->tag = t.tag;
  de->vr  = vr.vr;
  de->vl  = vl.vl;
  return 0;
}

static int read_explicit_undef( AVIOContext *pb, data_element * de )
{
  static const tag_t item_end = MAKE_TAG( 0xfffe,0xe00d );
  utag_t t;
  uvr_t vr;
  uvl_t vl;
  uvl16_t vl16;
  int ret;

  // Tag
  ret = avio_read(pb, (unsigned char*)t.tags, sizeof *t.tags * 2 );
  if( ret <= 0 ) return AVERROR(EIO);
  SWAP_TAG(t);
  av_assert0( tag_is_lower( de, t.tag ) );

  if( t.tag == item_end )
    {
    // Special case:
    ret = avio_read(pb, vl.bytes, 4);
    if( ret <= 0 ) return AVERROR(EIO);
    if( vl.vl != 0 ) return AVERROR_INVALIDDATA;
    vr.vr = E_INVALID;
    }
  else
    {
    // Value Representation
    av_assert0( get_group(t.tag) != 0xfffe );
    ret = avio_read(pb, vr.str, 2 );
    if( ret <= 0 ) return AVERROR(EIO);
    if( !isvr_valid(vr) ) return AVERROR_INVALIDDATA;

    // padding and/or 16bits VL
    ret = avio_read( pb, vl16.bytes, sizeof *vl16.bytes * 2 );
    if( ret <= 0 ) return AVERROR(EIO);

    // Value Length
    if( isvr32( vr.vr ) )
      {
      /* padding must be set to zero */
      if( vl16.vl16 != 0 ) return AVERROR_INVALIDDATA;

      ret = avio_read(pb, vl.bytes, 4 );
      if( ret <= 0 ) return AVERROR(EIO);
      SWAP_VL(vl.vl);
      }
    else
      {
      SWAP_VL16(vl16.vl16);
      vl.vl = vl16.vl16;
      }
    }
  de->tag = t.tag;
  de->vr  = vr.vr;
  de->vl  = vl.vl;
  return 0;
}

// implicit
static int read_implicit( AVIOContext * pb, data_element * de )
{
  utag_t t;
  uvl_t vl;
  int ret;

  // Tag
  ret = avio_read(pb, (unsigned char*)t.tags, sizeof *t.tags * 2 );
  if( ret <= 0 ) return AVERROR(EIO);
  SWAP_TAG(t);
  av_assert0( tag_is_lower( de, t.tag ) );

  // Value Length (always 32bits)
  ret = avio_read(pb, vl.bytes, 4);
  if( ret <= 0 ) return AVERROR(EIO);
  SWAP_VL(vl.vl);

  de->tag = t.tag;
  de->vr  = E_INVALID;
  de->vl  = vl.vl;
  return 0;
}

static inline int read_ul( AVIOContext *pb, uint32_t * value )
{
  int ret = avio_read(pb, (unsigned char*)value, sizeof *value );
  if( ret <= 0 ) return AVERROR(EIO);
  SWAP_VL(*value);
  return 0;
}

static int read_meta( AVIOContext *pb )
{
  uint32_t gl;
  data_element de = { 0 /* tag */ };
  int ret;
  ret = read_explicit( pb, &de );
  if( ret < 0 ) return ret;
  av_assert0( de.tag == MAKE_TAG(0x2,0x0) );
  av_assert0( de.vr == E_UL );
  av_assert0( de.vl == 4 );
  // file meta group length
  ret = read_ul( pb, &gl );
  if( ret < 0 ) return ret;
  // for now skip the meta header, we'll need to read whether DICOM contains
  // MPEG-2 or MP4 (or image!)
  avio_skip(pb, gl);
  av_log (NULL, AV_LOG_DEBUG, "Skipped: %d\n", gl );

  return 0;
}

static uint32_t read_sq_undef( AVIOContext * pb );
static uint32_t read_encapsulated_pixel_data( AVIOContext * pb );

/* read a single undefined length Item */
static uint32_t read_item_undef( AVIOContext * pb )
{
  data_element de = { 0 /* tag */ };
  uint32_t itemlen = 0;
  do
    {
    // carefully read an Item End or an Explicit Data Element:
    const int b = read_explicit_undef(pb, &de);
    av_assert0( b );
    if( is_end_item(&de) )
      {
      // end of Item
      itemlen += 4 /* tags */ + 4 /* VL */;
      break;
      }

    if( is_undef_len(&de) )
      {
      // Either undefined SQ or encapsulated Pixel Data:
      const int is_encapsulated = is_encapsulated_pixel_data( &de );
      if( is_encapsulated )
        {
        const uint32_t epdlen = read_encapsulated_pixel_data( pb );
        itemlen += compute_undef_len( &de, epdlen );
        }
      else
        {
        const uint32_t seqlen = read_sq_undef( pb );
        av_assert0( de.vr == E_SQ ); // IVRLE
        itemlen += compute_undef_len( &de, seqlen );
        }
      }
    else
      {
      itemlen += compute_len( &de );
      }
    } while( 1 );

  return itemlen;
}

/* read a single undefined length SQ */
/* return the actual length of the sequence */
static uint32_t read_sq_undef( AVIOContext * pb )
{
  data_element de;
  uint32_t seqlen = 0;
  do
    {
    int b;
    // restart tag for each new Item:
    de.tag = 0;
    // Item start
    b = read_implicit( pb, &de );
    av_assert0( b );
    if( is_end_sq(&de) )
      {
      /* end of SQ */
      av_assert0( de.vl == 0 );
      seqlen += 4 /* tag */ + 4 /* vl */;
      break;
      }
    av_assert0( is_start(&de) );

    if( is_undef_len(&de) )
      {
      const uint32_t itemlen = read_item_undef( pb );
      seqlen += 4 /* tag */ + 4 /* vl */ + itemlen;
      }
    else
      {
      seqlen += 4 /* tag */ + 4 /* vl */ + de.vl;
      // skip over an entire Item
      avio_skip(pb, de.vl);
      }
    } while( 1 );

  // post-condition
  av_assert0( is_end_sq(&de) );

  return seqlen;
}

/* Nested Icon SQ  (with encapsulated Pixel Data) */
static uint32_t read_encapsulated_pixel_data( AVIOContext * pb )
{
  data_element de;
  uint32_t epdlen = 0;
  do
    {
    int b;
    /* restart for each Item */
    de.tag = 0;
    /* Item start */
    b = read_implicit(pb, &de);
    av_assert0( b );
    /* end of SQ */
    epdlen += 4 /* tag */ + 4 /* vl */;
    if( is_end_sq(&de) ) break;
    av_assert0( is_start(&de) );

    avio_skip(pb, de.vl);
    epdlen += de.vl;
    } while( 1 );

  // post-condition
  av_assert0( is_end_sq(&de) );

  return epdlen;
}

static int read_dataset( AVIOContext * pb )
{
  static const tag_t pixel_data = MAKE_TAG( 0x7fe0,0x0010 );
  data_element de = { 0 /* tag */ };
  int ret;
  while( (ret = read_explicit( pb, &de)) == 0 && tag_is_lower( &de, pixel_data ) )
    {
    av_log (NULL, AV_LOG_DEBUG, "%d : %04x,%04x\n", pb->pos, get_group(de.tag), get_element(de.tag) );
    av_assert0( get_group( de.tag ) != 0xfffe );
    av_assert0( get_group( de.tag ) <= 0x7fe0 );
    if( is_undef_len(&de) )
      {
      if( de.vr != E_SQ )
        {
        av_assert0( de.vr == E_UN ); // IVRLE !
        av_assert0(0);
        }
      read_sq_undef(pb);
      }
    else
      {
      if( de.vr == E_SQ )
        {
        // skip over an entire SQ
        av_assert0( de.vr == E_SQ );
        avio_skip(pb, de.vl);
        }
      else
        {
        avio_skip(pb, de.vl);
        }
      }
    }
  return 0;
}

static int dicm_read_probe(AVProbeData *probe_packet)
{
    if (!memcmp(probe_packet->buf + 128, "DICM", 4))
        return AVPROBE_SCORE_MAX;
    return 0;
}

extern AVInputFormat ff_mov_demuxer;

static int dicm_read_header(AVFormatContext *ctx)
{
    DICMContext *dicm = ctx->priv_data;
    AVIOContext *pb = ctx->pb;
    AVStream *vst;
    AVInputFormat *sub_demuxer = NULL;
    AVFormatContext *sub_ctx;
    int ret;
    data_element de = { 0 };

    read_preamble(pb);
    read_meta(pb);
    read_dataset(pb);
    // read basic offset table:
    read_implicit( pb, &de );
    av_assert0( is_start(&de) );
    avio_skip(pb, de.vl);
    // read the Item start:
    de.tag = 0;
    read_implicit( pb, &de );
    av_assert0( is_start(&de) );

    //av_log (ctx, AV_LOG_DEBUG, "MPEG stream start here: %d\n", pb->pos );
    av_log (ctx, AV_LOG_DEBUG, "MPEG stream start here: %d length is: %d\n", pb->buf_ptr - pb->buffer, de.vl );
    //    AVProbeData pd;

    sub_demuxer = &ff_mov_demuxer;
#if 0
    if (!(sub_ctx = avformat_alloc_context())) {
      //ret = AVERROR(ENOMEM);
      av_assert0(0);
    }
    sub_ctx->pb       = pb;
    ret = avformat_open_input(&sub_ctx, "", sub_demuxer, NULL);
    av_assert0( ret == 0);
    sub_ctx->ctx_flags &= ~AVFMTCTX_NOHEADER;
    ret = avformat_find_stream_info(sub_ctx, NULL);
#else
    ret = avformat_open_input(&ctx, "", sub_demuxer, NULL);
    av_assert0( ret == 0);
#endif
    //av_assert0(0);

#if 0
    // open MP4 container:
    vst = avformat_new_stream(ctx, NULL);
    if (!vst)
        return AVERROR(ENOMEM);
    dicm->video_stream_index = vst->index;

    vst->codec->codec_type = AVMEDIA_TYPE_VIDEO;
    vst->codec->codec_id   = AV_CODEC_ID_MPEG4;
    vst->need_parsing      = AVSTREAM_PARSE_FULL;
    //avpriv_set_pts_info(vst, 64, 1, 100);
    avpriv_set_pts_info(vst, 64, 1, 15);
#endif

    return 0;
}

static int dicm_read_packet(AVFormatContext *s, AVPacket *pkt)
{
    av_assert0(0);
    return 0;
}

AVInputFormat ff_dicm_demuxer = {
    .name           = "dicm",
    .long_name      = NULL_IF_CONFIG_SMALL("DICOM Medicine"),
    .extensions     = "dcm",
    .priv_data_size = sizeof(DICMContext),
    .read_probe     = dicm_read_probe,
    .read_header    = dicm_read_header,
    .read_packet    = dicm_read_packet,
    .mime_type      = "application/dicom"
};

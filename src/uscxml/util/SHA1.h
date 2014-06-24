/**
 Copyright (C) 1998, 2009
 Paul E. Jones <paulej@packetizer.com>

 Freeware Public License (FPL)

 This software is licensed as "freeware."  Permission to distribute
 this software in source and binary forms, including incorporation
 into other products, is hereby granted without a fee.  THIS SOFTWARE
 IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESSED OR IMPLIED WARRANTIES,
 INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
 AND FITNESS FOR A PARTICULAR PURPOSE.  THE AUTHOR SHALL NOT BE HELD
 LIABLE FOR ANY DAMAGES RESULTING FROM THE USE OF THIS SOFTWARE, EITHER
 DIRECTLY OR INDIRECTLY, INCLUDING, BUT NOT LIMITED TO, LOSS OF DATA
 OR DATA BEING RENDERED INACCURATE.
*/

/*
 *  sha1.h
 *
 *  Copyright (C) 1998, 2009
 *  Paul E. Jones <paulej@packetizer.com>
 *  All Rights Reserved
 *
 *****************************************************************************
 *  $Id: sha1.h 12 2009-06-22 19:34:25Z paulej $
 *****************************************************************************
 *
 *  Description:
 *      This class implements the Secure Hashing Standard as defined
 *      in FIPS PUB 180-1 published April 17, 1995.
 *
 *      Many of the variable names in the SHA1Context, especially the
 *      single character names, were used because those were the names
 *      used in the publication.
 *
 *      Please read the file sha1.c for more information.
 *
 */

#ifndef _SHA1_H_
#define _SHA1_H_

#if defined(_WIN32) && !defined(USCXML_STATIC)
#	ifdef USCXML_EXPORT
#		define USCXML_API __declspec(dllexport)
#	else
#		define USCXML_API __declspec(dllimport)
#	endif
#else
#	define USCXML_API
#endif

#ifdef __cplusplus
extern "C" {
#endif

/*
 *  This structure will hold context information for the hashing
 *  operation
 */
typedef struct SHA1Context {
	unsigned Message_Digest[5]; /* Message Digest (output)          */

	unsigned Length_Low;        /* Message length in bits           */
	unsigned Length_High;       /* Message length in bits           */

	unsigned char Message_Block[64]; /* 512-bit message blocks      */
	int Message_Block_Index;    /* Index into message block array   */

	int Computed;               /* Is the digest computed?          */
	int Corrupted;              /* Is the message digest corruped?  */
} SHA1Context;

/*
 *  Function Prototypes
 */
USCXML_API void SHA1Reset(SHA1Context *);
USCXML_API int SHA1Result(SHA1Context *);
USCXML_API void SHA1Input(SHA1Context *,
                          const unsigned char *,
                          unsigned);

#ifdef __cplusplus
}
#endif

#endif

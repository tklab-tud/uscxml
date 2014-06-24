/*
cdecode.h - c header for a base64 decoding algorithm

This is part of the libb64 project, and has been placed in the public domain.
For details, see http://sourceforge.net/projects/libb64
*/

#ifndef BASE64_H_MMR5NHB7
#define BASE64_H_MMR5NHB7

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

/// DECODE

typedef enum {
	step_a, step_b, step_c, step_d
}
base64_decodestep;

typedef struct {
	base64_decodestep step;
	char plainchar;
} base64_decodestate;

USCXML_API void base64_init_decodestate(base64_decodestate* state_in);
USCXML_API int base64_decode_value(char value_in);
USCXML_API int base64_decode_block(const char* code_in, const int length_in, char* plaintext_out, base64_decodestate* state_in);

/// ENDCODE

typedef enum {
	step_A, step_B, step_C
} base64_encodestep;

typedef struct {
	base64_encodestep step;
	char result;
	int stepcount;
} base64_encodestate;

USCXML_API void base64_init_encodestate(base64_encodestate* state_in);
USCXML_API char base64_encode_value(char value_in);
USCXML_API int base64_encode_block(const char* plaintext_in, int length_in, char* code_out, base64_encodestate* state_in);
USCXML_API int base64_encode_blockend(char* code_out, base64_encodestate* state_in);

#ifdef __cplusplus
}
#endif


#endif /* end of include guard: BASE64_H_MMR5NHB7 */

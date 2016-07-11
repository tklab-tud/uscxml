#define protected public
#include "uscxml/util/URL.h"
#include "uscxml/plugins/datamodel/c89/C89DataModel.h"
#include "uscxml/plugins/datamodel/c89/C89Parser.h"

#include <iostream>

using namespace uscxml;

extern int c89_debug;

void testC89Parser() {

	c89_debug = 0;

    std::list<std::string> localTest = {
    "int main() { a = 10; }"
    };
    
    for (auto test : localTest) {
        try {
            C89Parser ast(test);
            ast.dump();
        } catch (Event e) {
            std::cerr << e << std::endl;
        }
    }

    assert(false);
    
    std::list<URL> remoteTests = {
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/00_assignment.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/01_comment.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/02_printf.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/03_struct.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/04_for.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/05_array.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/06_case.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/07_function.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/08_while.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/09_do_while.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/10_pointer.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/11_precedence.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/12_hashdefine.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/13_integer_literals.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/14_if.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/15_recursion.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/16_nesting.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/17_enum.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/18_include.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/19_pointer_arithmetic.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/20_pointer_comparison.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/21_char_array.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/22_floating_point.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/23_type_coercion.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/24_math_library.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/25_quicksort.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/26_character_constants.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/27_sizeof.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/28_strings.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/29_array_address.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/30_hanoi.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/31_args.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/32_led.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/33_ternary_op.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/34_array_assignment.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/35_sizeof.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/36_array_initialisers.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/37_sprintf.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/38_multiple_array_index.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/39_typedef.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/40_stdio.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/41_hashif.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/42_function_pointer.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/43_void_param.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/44_scoped_declarations.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/45_empty_for.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/46_grep.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/47_switch_return.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/48_nested_break.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/49_bracket_evaluation.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/50_logical_second_arg.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/51_static.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/52_unnamed_enum.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/54_goto.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/55_array_initialiser.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/56_cross_structure.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/57_macro_bug.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/58_return_outside.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/59_break_before_loop.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/60_local_vars.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/61_initializers.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/62_float.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/63_typedef.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/64_double_prefix_op.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/65_typeless.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/66_printf_undefined.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/67_macro_crash.c"),
        URL("https://raw.githubusercontent.com/zsaleeba/picoc/master/tests/68_return.c")
    };
    
    for (auto testURL : remoteTests) {
		try {
            std::cout << std::endl << "'" << (std::string)testURL << "':" << std::endl;
            std::cout << testURL.getInContent() << std::endl;
            
			C89Parser ast(testURL.getInContent());
			ast.dump();
            
		} catch (Event e) {
			std::cerr << e << std::endl;
		}
        std::this_thread::sleep_for(std::chrono::seconds(10));
	}

}

int main(int argc, char** argv) {
	testC89Parser();
}
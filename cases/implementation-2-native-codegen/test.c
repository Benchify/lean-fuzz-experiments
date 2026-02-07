// Lean compiler output
// Module: test
// Imports: public import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_testArray;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_testArray___closed__2;
static lean_object* l_testArray___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_testArray___closed__3;
static lean_object* l_largeCalc___closed__0;
LEAN_EXPORT lean_object* l_tailRecTest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_complexMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_strTest;
LEAN_EXPORT lean_object* l_getElement___boxed(lean_object*);
LEAN_EXPORT lean_object* l_getElement(lean_object*);
LEAN_EXPORT lean_object* l_complexMatch___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_testArray___closed__0;
static lean_object* l_strTest___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_largeCalc;
static lean_object* _init_l_largeCalc___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("999999999999999998000000000000000001");
return x_1;
}
}
static lean_object* _init_l_largeCalc() {
_start:
{
lean_object* x_1; 
x_1 = l_largeCalc___closed__0;
return x_1;
}
}
static lean_object* _init_l_testArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_testArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_testArray___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_testArray___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_testArray___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_testArray___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_testArray___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_testArray() {
_start:
{
lean_object* x_1; 
x_1 = l_testArray___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_getElement(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_testArray;
x_4 = lean_array_get(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_getElement___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_getElement(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_tailRecTest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_complexMatch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_nat_add(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(2u);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_complexMatch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_complexMatch(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_strTest___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testing", 7, 7);
return x_1;
}
}
static lean_object* _init_l_strTest() {
_start:
{
lean_object* x_1; 
x_1 = l_strTest___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_test(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_largeCalc___closed__0 = _init_l_largeCalc___closed__0();
lean_mark_persistent(l_largeCalc___closed__0);
l_largeCalc = _init_l_largeCalc();
lean_mark_persistent(l_largeCalc);
l_testArray___closed__0 = _init_l_testArray___closed__0();
lean_mark_persistent(l_testArray___closed__0);
l_testArray___closed__1 = _init_l_testArray___closed__1();
lean_mark_persistent(l_testArray___closed__1);
l_testArray___closed__2 = _init_l_testArray___closed__2();
lean_mark_persistent(l_testArray___closed__2);
l_testArray___closed__3 = _init_l_testArray___closed__3();
lean_mark_persistent(l_testArray___closed__3);
l_testArray = _init_l_testArray();
lean_mark_persistent(l_testArray);
l_strTest___closed__0 = _init_l_strTest___closed__0();
lean_mark_persistent(l_strTest___closed__0);
l_strTest = _init_l_strTest();
lean_mark_persistent(l_strTest);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

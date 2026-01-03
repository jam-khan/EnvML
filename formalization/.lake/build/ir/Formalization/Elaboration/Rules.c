// Lean compiler output
// Module: Formalization.Elaboration.Rules
// Imports: Init Formalization.ENVCAP.Syntax Formalization.LambdaE.Syntax
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
LEAN_EXPORT lean_object* l_ENVCAP_ElaborateType(lean_object*);
LEAN_EXPORT lean_object* l_ENVCAP_ElaborateType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
case 1:
{
lean_object* x_9; 
x_9 = lean_box(1);
return x_9;
}
case 3:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_ENVCAP_ElaborateType(x_11);
x_14 = l_ENVCAP_ElaborateType(x_12);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_ENVCAP_ElaborateType(x_15);
x_18 = l_ENVCAP_ElaborateType(x_16);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
case 4:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 1);
x_22 = l_ENVCAP_ElaborateType(x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_ENVCAP_ElaborateType(x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
default: 
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_2 = x_27;
x_3 = x_28;
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_ENVCAP_ElaborateType(x_2);
x_5 = l_ENVCAP_ElaborateType(x_3);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Formalization_ENVCAP_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Formalization_LambdaE_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Formalization_Elaboration_Rules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Formalization_ENVCAP_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Formalization_LambdaE_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

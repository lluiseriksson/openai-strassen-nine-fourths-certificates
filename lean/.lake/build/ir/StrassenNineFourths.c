// Lean compiler output
// Module: StrassenNineFourths
// Imports: public import Init public meta import Init
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_once_cell_t lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0;
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt(lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_cube(lean_object*);
static lean_once_cell_t lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0;
static lean_once_cell_t lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1;
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0;
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleZWeight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_delta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_diagVal(lean_object*, lean_object*);
static lean_once_cell_t lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0;
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_Hval(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt(lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_n_3_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_add(lean_object* v_x_6_, lean_object* v_y_7_){
_start:
{
lean_object* v_num_8_; lean_object* v_den_9_; lean_object* v_num_10_; lean_object* v_den_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_22_; 
v_num_8_ = lean_ctor_get(v_x_6_, 0);
v_den_9_ = lean_ctor_get(v_x_6_, 1);
v_num_10_ = lean_ctor_get(v_y_7_, 0);
v_den_11_ = lean_ctor_get(v_y_7_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v_y_7_);
if (v_isSharedCheck_22_ == 0)
{
v___x_13_ = v_y_7_;
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_den_11_);
lean_inc(v_num_10_);
lean_dec(v_y_7_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_22_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_15_ = lean_int_mul(v_num_8_, v_den_11_);
v___x_16_ = lean_int_mul(v_num_10_, v_den_9_);
lean_dec(v_num_10_);
v___x_17_ = lean_int_add(v___x_15_, v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_int_mul(v_den_9_, v_den_11_);
lean_dec(v_den_11_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_18_);
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_add___boxed(lean_object* v_x_23_, lean_object* v_y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_add(v_x_23_, v_y_24_);
lean_dec_ref(v_x_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_sub(lean_object* v_x_26_, lean_object* v_y_27_){
_start:
{
lean_object* v_num_28_; lean_object* v_den_29_; lean_object* v_num_30_; lean_object* v_den_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
v_num_28_ = lean_ctor_get(v_x_26_, 0);
v_den_29_ = lean_ctor_get(v_x_26_, 1);
v_num_30_ = lean_ctor_get(v_y_27_, 0);
v_den_31_ = lean_ctor_get(v_y_27_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_y_27_);
if (v_isSharedCheck_42_ == 0)
{
v___x_33_ = v_y_27_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_den_31_);
lean_inc(v_num_30_);
lean_dec(v_y_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_35_ = lean_int_mul(v_num_28_, v_den_31_);
v___x_36_ = lean_int_mul(v_num_30_, v_den_29_);
lean_dec(v_num_30_);
v___x_37_ = lean_int_sub(v___x_35_, v___x_36_);
lean_dec(v___x_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_int_mul(v_den_29_, v_den_31_);
lean_dec(v_den_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_38_);
lean_ctor_set(v___x_33_, 0, v___x_37_);
v___x_40_ = v___x_33_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_sub___boxed(lean_object* v_x_43_, lean_object* v_y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_sub(v_x_43_, v_y_44_);
lean_dec_ref(v_x_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_mul(lean_object* v_x_46_, lean_object* v_y_47_){
_start:
{
lean_object* v_num_48_; lean_object* v_den_49_; lean_object* v_num_50_; lean_object* v_den_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_60_; 
v_num_48_ = lean_ctor_get(v_x_46_, 0);
v_den_49_ = lean_ctor_get(v_x_46_, 1);
v_num_50_ = lean_ctor_get(v_y_47_, 0);
v_den_51_ = lean_ctor_get(v_y_47_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_y_47_);
if (v_isSharedCheck_60_ == 0)
{
v___x_53_ = v_y_47_;
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_den_51_);
lean_inc(v_num_50_);
lean_dec(v_y_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_55_ = lean_int_mul(v_num_48_, v_num_50_);
lean_dec(v_num_50_);
v___x_56_ = lean_int_mul(v_den_49_, v_den_51_);
lean_dec(v_den_51_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_56_);
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_58_ = v___x_53_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_mul___boxed(lean_object* v_x_61_, lean_object* v_y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_mul(v_x_61_, v_y_62_);
lean_dec_ref(v_x_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_QRat_cube(lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_inc_ref(v_x_64_);
v___x_65_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_mul(v_x_64_, v_x_64_);
v___x_66_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_mul(v___x_65_, v_x_64_);
lean_dec_ref(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight(lean_object* v_a_71_, lean_object* v_h_72_, lean_object* v_y_73_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_int_dec_le(v_h_72_, v_y_73_);
if (v___x_76_ == 0)
{
goto v___jp_74_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_77_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1, &lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1);
v___x_78_ = lean_int_mul(v___x_77_, v_h_72_);
v___x_79_ = lean_int_add(v___x_78_, v_a_71_);
lean_dec(v___x_78_);
v___x_80_ = lean_int_sub(v___x_79_, v___x_77_);
lean_dec(v___x_79_);
v___x_81_ = lean_int_dec_le(v_y_73_, v___x_80_);
lean_dec(v___x_80_);
if (v___x_81_ == 0)
{
goto v___jp_74_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0);
return v___x_82_;
}
}
v___jp_74_:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___boxed(lean_object* v_a_83_, lean_object* v_h_84_, lean_object* v_y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_StrassenNineFourths_StrassenNineFourths_middleYWeight(v_a_83_, v_h_84_, v_y_85_);
lean_dec(v_y_85_);
lean_dec(v_h_84_);
lean_dec(v_a_83_);
return v_res_86_;
}
}
static lean_object* _init_lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0);
v___x_88_ = lean_int_neg(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleZWeight(lean_object* v_a_89_, lean_object* v_h_90_, lean_object* v_z_91_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_94_ = lean_int_add(v_h_90_, v_a_89_);
v___x_95_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0);
v___x_96_ = lean_int_sub(v___x_94_, v___x_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_int_dec_le(v___x_96_, v_z_91_);
lean_dec(v___x_96_);
if (v___x_97_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_98_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1, &lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1);
v___x_99_ = lean_int_mul(v___x_98_, v_h_90_);
v___x_100_ = lean_int_add(v___x_99_, v_a_89_);
lean_dec(v___x_99_);
v___x_101_ = lean_int_sub(v___x_100_, v___x_98_);
lean_dec(v___x_100_);
v___x_102_ = lean_int_dec_le(v_z_91_, v___x_101_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___closed__0);
return v___x_103_;
}
}
v___jp_92_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__0);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_middleZWeight___boxed(lean_object* v_a_104_, lean_object* v_h_105_, lean_object* v_z_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_StrassenNineFourths_StrassenNineFourths_middleZWeight(v_a_104_, v_h_105_, v_z_106_);
lean_dec(v_z_106_);
lean_dec(v_h_105_);
lean_dec(v_a_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_delta(lean_object* v_sp_108_, lean_object* v_a_109_, lean_object* v_h_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_h_110_, v___x_111_);
lean_inc_ref(v_sp_108_);
lean_inc(v_a_109_);
v___x_113_ = lean_apply_2(v_sp_108_, v_a_109_, v___x_112_);
v___x_114_ = lean_apply_2(v_sp_108_, v_a_109_, v_h_110_);
v___x_115_ = lp_StrassenNineFourths_StrassenNineFourths_QRat_sub(v___x_113_, v___x_114_);
lean_dec_ref(v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_diagVal(lean_object* v_sp_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; 
lean_inc(v_a_117_);
v___x_118_ = lean_apply_2(v_sp_116_, v_a_117_, v_a_117_);
return v___x_118_;
}
}
static lean_object* _init_lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(3u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg(lean_object* v_sp_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; lean_object* v_num_124_; lean_object* v_den_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_140_; 
lean_inc_n(v_a_122_, 2);
v___x_123_ = lean_apply_2(v_sp_121_, v_a_122_, v_a_122_);
v_num_124_ = lean_ctor_get(v___x_123_, 0);
v_den_125_ = lean_ctor_get(v___x_123_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_140_ == 0)
{
v___x_127_ = v___x_123_;
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_den_125_);
lean_inc(v_num_124_);
lean_dec(v___x_123_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_129_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1, &lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1_once, _init_lp_StrassenNineFourths_StrassenNineFourths_middleYWeight___closed__1);
v___x_130_ = lean_int_mul(v___x_129_, v_num_124_);
lean_dec(v_num_124_);
v___x_131_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg___closed__0);
v___x_132_ = lean_nat_to_int(v_a_122_);
v___x_133_ = lean_int_mul(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
v___x_134_ = lean_obj_once(&lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0, &lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0_once, _init_lp_StrassenNineFourths_StrassenNineFourths_QRat_ofInt___closed__0);
v___x_135_ = lean_int_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_int_mul(v___x_135_, v_den_125_);
lean_dec(v_den_125_);
lean_dec(v___x_135_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_136_);
lean_ctor_set(v___x_127_, 0, v___x_130_);
v___x_138_ = v___x_127_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* lp_StrassenNineFourths_StrassenNineFourths_Hval(lean_object* v_sp_141_, lean_object* v_a_142_, lean_object* v_ha_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lp_StrassenNineFourths_StrassenNineFourths_Hval___redArg(v_sp_141_, v_a_142_);
return v___x_144_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_StrassenNineFourths_StrassenNineFourths(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

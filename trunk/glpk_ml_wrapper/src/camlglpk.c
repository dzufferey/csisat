/*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *  Copyright (C) 2007-2008  The CSIsat team
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  For information about the CSIsat project,
 *  please visit the CSIsat web page at:
 *  http://www.cs.sfu.ca/~dbeyer/CSIsat/

 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <glpk.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>   

void no_output()
{
    glp_term_out(GLP_OFF);
}

value lp_create(value unit)
{
    CAMLparam1(unit);
    LPX* lp = lpx_create_prob();
    CAMLreturn ((value)lp);
}

value lp_delete(value lp)
{
    CAMLparam1(lp);
    lpx_delete_prob((LPX*)lp);   
    CAMLreturn (Val_unit);
}


value lp_set_maximize(value lp)
{
    CAMLparam1(lp);
    lpx_set_obj_dir((LPX*)lp, LPX_MAX);
    CAMLreturn (Val_unit);
}

value lp_set_minimize(value lp)
{
    CAMLparam1(lp);
    lpx_set_obj_dir((LPX*)lp, LPX_MIN);
    CAMLreturn (Val_unit);
}

value lp_add_row(value lp, value i)
{
    CAMLparam2(lp,i);
    lpx_add_rows((LPX*)lp, Int_val(i));
    CAMLreturn (Val_unit);
}

value lp_add_col(value lp, value i)
{
    CAMLparam2(lp,i);
    lpx_add_cols((LPX*)lp, Int_val(i));
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_free(value lp, value i)
{
    CAMLparam2(lp,i);
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_FR, 0.0, 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_lower(value lp, value i, value lo)
{
    CAMLparam3(lp,i,lo);
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_LO, Double_val(lo), 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_upper(value lp, value i, value up)
{
    CAMLparam3(lp,i,up);
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_UP, 0.0, Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_double(value lp, value i, value lo, value up)
{
    CAMLparam4(lp,i,lo,up);
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_DB, Double_val(lo), Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_fixed(value lp, value i, value x)
{
    CAMLparam3(lp,i,x);
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_FX, Double_val(x), Double_val(x) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_free(value lp, value i)
{
    CAMLparam2(lp,i);
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_FR, 0.0, 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_lower(value lp, value i, value lo)
{
    CAMLparam3(lp,i,lo);
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_LO, Double_val(lo), 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_upper(value lp, value i, value up)
{
    CAMLparam3(lp,i,up);
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_UP, 0.0, Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_double(value lp, value i, value lo, value up)
{
    CAMLparam4(lp,i,lo,up);
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_DB, Double_val(lo), Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_fixed(value lp, value i, value x)
{
    CAMLparam3(lp,i,x);
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_FX, Double_val(x), Double_val(x) );
    CAMLreturn (Val_unit);
}

value lp_set_obj_coef(value lp, value i, value coeff)
{
    CAMLparam3(lp,i,coeff);
    lpx_set_obj_coef((LPX*)lp, Int_val(i) + 1, Double_val(coeff));
    CAMLreturn (Val_unit);
}

value lp_set_mat_row(value lp, value i, value len, value array)
{
    CAMLparam4(lp,i,len,array);
    int length = Int_val(len);
    int * indexes = malloc((len + 1) * sizeof(int));
    double *val =  malloc((len + 1) * sizeof(double));
    int non_zero = 0;
    int k;
    for(k = 0; k < length; ++k){
        double entry = Double_field(array, k);
        if(entry != 0){
            ++non_zero;
            indexes[non_zero] = k+1;
            val[non_zero] = entry;
        }
    }
    if(non_zero > 0){
        lpx_set_mat_row((LPX*)lp, Int_val(i) + 1, non_zero, indexes, val);
    }
    free(indexes);
    free(val);
    CAMLreturn (Val_unit);
}

value lp_set_mat_col(value lp, value i, value len, value array)
{
    CAMLparam4(lp,i,len,array);
    int length = Int_val(len);
    int * indexes = malloc((len + 1) * sizeof(int));
    double *val =  malloc((len + 1) * sizeof(double));
    int non_zero = 0;
    int k;
    for(k = 0; k < length; ++k){
        double entry = Double_field(array, k);
        if(entry != 0){
            ++non_zero;
            indexes[non_zero] = k+1;
            val[non_zero] = entry;
        }
    }
    if(non_zero > 0){
        lpx_set_mat_col((LPX*)lp, Int_val(i) + 1, non_zero, indexes, val);
    }
    free(indexes);
    free(val);
    CAMLreturn (Val_unit);
}


value lp_simplex(value lp, value presolve)
{
    CAMLparam2(lp,presolve);
    if(Bool_val(presolve)){
        lpx_set_int_parm((LPX*)lp, LPX_K_PRESOL, 1);
    }else{
        lpx_set_int_parm((LPX*)lp, LPX_K_PRESOL, 0);
    }
    no_output();
    int status = lpx_simplex((LPX*)lp);
    value val = Val_false;
    if(status == LPX_E_OK){
        val = Val_true;
    }else if (status == LPX_E_FAULT){
        //fprintf(stderr, "solving failed \n");
    }else if (status == LPX_E_OBJLL){
        //fprintf(stderr, "unbounded (lower)\n");
    }else if (status == LPX_E_OBJUL){
        //fprintf(stderr, "unbounded (upper)\n");
    }else if (status == LPX_E_ITLIM){
        //fprintf(stderr, "iteration limit reached\n");
    }else if (status == LPX_E_TMLIM){
        //fprintf(stderr, "time limit reached\n");
    }else if (status == LPX_E_SING){
        fprintf(stderr, "singular or ill-conditionned matrix\n");
    }else if (status == LPX_E_NOPFS){
        //fprintf(stderr, "no primal solution\n");
    }else if (status == LPX_E_NODFS){
        //fprintf(stderr, "no dual solution\n");
    }else{
        fprintf(stderr, "unknown status: %d\n", status);
    }
    CAMLreturn (val);
}

value lp_simplex_exact(value lp)
{
    CAMLparam1(lp);
    no_output();
    lpx_simplex((LPX*)lp);
    int status = lpx_exact((LPX*)lp);
    value val = Val_false;
    if(status == LPX_E_OK){
        val = Val_true;
    }else if (status == LPX_E_FAULT){
        //fprintf(stderr, "solving failed \n");
    }else if (status == LPX_E_OBJLL){
        //fprintf(stderr, "unbounded (lower)\n");
    }else if (status == LPX_E_OBJUL){
        //fprintf(stderr, "unbounded (upper)\n");
    }else if (status == LPX_E_ITLIM){
        //fprintf(stderr, "iteration limit reached\n");
    }else if (status == LPX_E_TMLIM){
        //fprintf(stderr, "time limit reached\n");
    }else if (status == LPX_E_SING){
        fprintf(stderr, "singular or ill-conditionned matrix\n");
    }else if (status == LPX_E_NOPFS){
        //fprintf(stderr, "no primal solution\n");
    }else if (status == LPX_E_NODFS){
        //fprintf(stderr, "no dual solution\n");
    }else{
        fprintf(stderr, "unknown status: %d\n", status);
    }
    CAMLreturn (val);
}
value lp_get_stat(value lp)
{
    CAMLparam1(lp);
    int status = lpx_get_status((LPX*)lp);
    CAMLreturn (Val_int(status));
}


value lp_get_obj_val(value lp)
{
    CAMLparam1(lp);
    double status = lpx_get_obj_val((LPX*)lp);
    CAMLreturn (caml_copy_double(status));
}

value lp_get_row_stat(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = lpx_get_row_stat((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (Val_int(status));
}

value lp_is_col_basic(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_col_stat((LPX*)lp, Int_val(i) + 1);
    value val = Val_false;
    if(status == GLP_BS ) {
      val = Val_true;
    }
    CAMLreturn (val);
}

value lp_is_row_basic(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_row_stat((LPX*)lp, Int_val(i) + 1);
    value val = Val_false;
    if(status == GLP_BS ) {
      val = Val_true;
    }
    CAMLreturn (val);
}

value lp_get_row_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_get_row_prim((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_rows_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_row_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}


value lp_get_row_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_get_row_dual((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_rows_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_row_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_get_col_stat(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = lpx_get_col_stat((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (Val_int(status));
}

value lp_get_col_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_get_col_prim((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_cols_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_col_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_get_col_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_get_col_dual((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_cols_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_col_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_interior(value lp)
{
    CAMLparam1(lp);
    no_output();
    int status = lpx_interior((LPX*)lp);
    value val = Val_false;
    if(status == LPX_E_OK){
        val = Val_true;
    }else if (status == LPX_E_FAULT){
        //fprintf(stderr, "solving failed \n");
    }else if (status == LPX_E_NOFEAS){
        //fprintf(stderr, "unfeasible system\n");
    }else if (status == LPX_E_NOCONV){
        fprintf(stderr, "slow convergence (or diverge)\n");
    }else if (status == LPX_E_ITLIM){
        fprintf(stderr, "iteration limit reached\n");
    }else if (status == LPX_E_INSTAB){
        fprintf(stderr, "numerical instability\n");
    }else{
        fprintf(stderr, "unknown status: %d\n", status);
    }
    CAMLreturn (val);
}

value lp_ipt_obj_val(value lp)
{
    CAMLparam1(lp);
    double status = lpx_ipt_obj_val((LPX*)lp);
    CAMLreturn (caml_copy_double(status));
}

value lp_ipt_row_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_ipt_row_prim((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_rows_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_row_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_row_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_ipt_row_dual((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_rows_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_row_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_col_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_ipt_col_prim((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_cols_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_col_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_col_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = lpx_ipt_col_dual((LPX*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_cols_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_col_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_dump_problem(value lp)
{
    CAMLparam1(lp);
    lpx_print_prob((LPX*)lp, "lp_error.debug");
    lpx_write_cpxlp((LPX*)lp, "cpxlp_error.debug");
    CAMLreturn (Val_unit);
}

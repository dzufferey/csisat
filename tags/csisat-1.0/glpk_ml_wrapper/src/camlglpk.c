/*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <glpk.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>   

int std_out;
int std_err;
void to_dev_null()
{
    int fnull = open("/dev/null", O_WRONLY);
    if (fnull == -1){
        perror("opening '/dev/null'");
        exit(-1);
    }
    fflush(stdout);
    dup2(STDOUT_FILENO, std_out);
    dup2(fnull, STDOUT_FILENO);//redirect stdout to /dev/null
    //fflush(stderr);
    //dup2(STDERR_FILENO, std_err);
    //dup2(fnull, STDERR_FILENO);//redirect stdout to /dev/null
    if(close(fnull) != 0){
        perror("closing '/dev/null'");
    }
}
void to_std_out()
{
    fflush(stdout);
    dup2(std_out, STDOUT_FILENO);
    //fflush(stderr);
    //dup2(std_err, STDERR_FILENO);
}

CAMLprim value lp_create(value unit)
{
    LPX* lp = lpx_create_prob();
    return (value)lp;
}

CAMLprim value lp_delete(value lp)
{
    lpx_delete_prob((LPX*)lp);   
    return Val_unit;
}


CAMLprim value lp_set_maximize(value lp)
{
    lpx_set_obj_dir((LPX*)lp, LPX_MAX);
    return Val_unit;
}

CAMLprim value lp_set_minimize(value lp)
{
    lpx_set_obj_dir((LPX*)lp, LPX_MIN);
    return Val_unit;
}

CAMLprim value lp_add_row(value lp, value i)
{
    lpx_add_rows((LPX*)lp, Int_val(i));
    return Val_unit;
}

CAMLprim value lp_add_col(value lp, value i)
{
    lpx_add_cols((LPX*)lp, Int_val(i));
    return Val_unit;
}

CAMLprim value lp_set_row_bnd_free(value lp, value i)
{
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_FR, 0.0, 0.0 );
    return Val_unit;
}

CAMLprim value lp_set_row_bnd_lower(value lp, value i, value lo)
{
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_LO, Double_val(lo), 0.0 );
    return Val_unit;
}

CAMLprim value lp_set_row_bnd_upper(value lp, value i, value up)
{
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_UP, 0.0, Double_val(up) );
    return Val_unit;
}

CAMLprim value lp_set_row_bnd_double(value lp, value i, value lo, value up)
{
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_DB, Double_val(lo), Double_val(up) );
    return Val_unit;
}

CAMLprim value lp_set_row_bnd_fixed(value lp, value i, value x)
{
    lpx_set_row_bnds((LPX*)lp, Int_val(i) + 1, LPX_FX, Double_val(x), Double_val(x) );
    return Val_unit;
}



CAMLprim value lp_set_col_bnd_free(value lp, value i)
{
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_FR, 0.0, 0.0 );
    return Val_unit;
}

CAMLprim value lp_set_col_bnd_lower(value lp, value i, value lo)
{
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_LO, Double_val(lo), 0.0 );
    return Val_unit;
}

CAMLprim value lp_set_col_bnd_upper(value lp, value i, value up)
{
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_UP, 0.0, Double_val(up) );
    return Val_unit;
}

CAMLprim value lp_set_col_bnd_double(value lp, value i, value lo, value up)
{
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_DB, Double_val(lo), Double_val(up) );
    return Val_unit;
}

CAMLprim value lp_set_col_bnd_fixed(value lp, value i, value x)
{
    lpx_set_col_bnds((LPX*)lp, Int_val(i) + 1, LPX_FX, Double_val(x), Double_val(x) );
    return Val_unit;
}

CAMLprim value lp_set_obj_coef(value lp, value i, value coeff)
{
    lpx_set_obj_coef((LPX*)lp, Int_val(i) + 1, Double_val(coeff));
    return Val_unit;
}

CAMLprim value lp_set_mat_row(value lp, value i, value len, value array)
{
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
    return Val_unit;
}

CAMLprim value lp_set_mat_col(value lp, value i, value len, value array)
{
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
    return Val_unit;
}


CAMLprim value lp_simplex(value lp, value presolve)
{
    if(Bool_val(presolve)){
        lpx_set_int_parm((LPX*)lp, LPX_K_PRESOL, 1);
    }else{
        lpx_set_int_parm((LPX*)lp, LPX_K_PRESOL, 0);
    }
    to_dev_null();
    int status = lpx_simplex((LPX*)lp);
    to_std_out();
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
    return val;
}

CAMLprim value lp_get_stat(value lp)
{
    int status = lpx_get_status((LPX*)lp);
    return Val_int(status);
}


CAMLprim value lp_get_obj_val(value lp)
{
    double status = lpx_get_obj_val((LPX*)lp);
    return caml_copy_double(status);
}

CAMLprim value lp_get_row_stat(value lp, value i)
{
    int status = lpx_get_row_stat((LPX*)lp, Int_val(i) + 1);
    return Val_int(status);
}

CAMLprim value lp_get_row_primal(value lp, value i)
{
    double val = lpx_get_row_prim((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_get_rows_primal(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_row_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}


CAMLprim value lp_get_row_dual(value lp, value i)
{
    double val = lpx_get_row_dual((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_get_rows_dual(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_row_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_get_col_stat(value lp, value i)
{
    int status = lpx_get_col_stat((LPX*)lp, Int_val(i) + 1);
    return Val_int(status);
}

CAMLprim value lp_get_col_primal(value lp, value i)
{
    double val = lpx_get_col_prim((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_get_cols_primal(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_col_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_get_col_dual(value lp, value i)
{
    double val = lpx_get_col_dual((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_get_cols_dual(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_get_col_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_interior(value lp)
{
    to_dev_null();
    int status = lpx_interior((LPX*)lp);
    to_std_out();
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
    return val;
}

CAMLprim value lp_ipt_obj_val(value lp)
{
    double status = lpx_ipt_obj_val((LPX*)lp);
    return caml_copy_double(status);
}

CAMLprim value lp_ipt_row_primal(value lp, value i)
{
    double val = lpx_ipt_row_prim((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_ipt_rows_primal(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_row_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_ipt_row_dual(value lp, value i)
{
    double val = lpx_ipt_row_dual((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_ipt_rows_dual(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_row_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_ipt_col_primal(value lp, value i)
{
    double val = lpx_ipt_col_prim((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_ipt_cols_primal(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_col_prim((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_ipt_col_dual(value lp, value i)
{
    double val = lpx_ipt_col_dual((LPX*)lp, Int_val(i) + 1);
    return caml_copy_double(val);
}

CAMLprim value lp_ipt_cols_dual(value lp, value length, value array)
{
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = lpx_ipt_col_dual((LPX*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    return Val_unit;
}

CAMLprim value lp_dump_problem(value lp)
{
    lpx_print_prob((LPX*)lp, "lp_error.debug");
    lpx_write_cpxlp((LPX*)lp, "cpxlp_error.debug");
    return Val_unit;
}

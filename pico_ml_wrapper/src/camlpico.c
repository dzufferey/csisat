/*  CSIsat: Interpolating decision procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
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
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <picosat.h>

/* the methods comment were directly taken from 'picosat.h' */

CAMLprim value unknown(){ return Val_int(PICOSAT_UNKNOWN);}
CAMLprim value satisfiable(){ return Val_int(PICOSAT_SATISFIABLE);}
CAMLprim value unsatisfiable(){ return Val_int(PICOSAT_UNSATISFIABLE);}
/*------------------------------------------------------------------------*/

CAMLprim value init(value unit)
{
    picosat_init();   
    return Val_unit;
}

CAMLprim value reset(value unit)
{
    picosat_reset();   
    return Val_unit;
}

/*------------------------------------------------------------------------*/

/* Set a seed for the random number generator.  The random number generator
 * is currently just used for generating random decisions.  In our
 * experiments having random decisions did not really help on industrial
 * examples, but was rather helpful to randomize the solver in order to
 * do proper benchmarking of different internal parameter sets.
 */
CAMLprim value set_seed(value seed)
{
    picosat_set_seed(Unsigned_int_val(seed));
    return Val_unit;
}

/* If you ever want to extract cores or proof traces with the current
 * instance of PicoSAT initialized with 'picosat_init', then make sure to
 * call 'picosat_enable_trace_generation' right after 'picosat_init'.
 */
CAMLprim value enable_trace(value unit)
{
    picosat_enable_trace_generation();
    return Val_unit;
}

/*------------------------------------------------------------------------*/
/* If you know a good estimate on how many variables you are going to use
 * then calling this function before adding literals will result in less
 * resizing of the variable table.  But this is just a minor optimization.
 */
CAMLprim value adjust(value n)
{
    picosat_adjust(Int_val(n));
    return Val_unit;
}

/*------------------------------------------------------------------------*/
/* Statistics.
 */
CAMLprim value second(value unit)
{
    return caml_copy_double(picosat_seconds());
}

/*------------------------------------------------------------------------*/
/* Add a literal of the next clause.  A zero terminates the clause.  The
 * solver is incremental.  Adding a new literal will reset the previous
 * assignment.
 */
CAMLprim value add(value i)
{
    picosat_add(Int_val(i));
    return Val_unit;
}

/* You can add arbitrary many assertions before the next 'picosat_sat'.
 * An assumption is only valid for the next 'picosat_sat' and will be taken
 * back afterwards.  Adding a new assumption will reset the previous
 * assignment.
 */
CAMLprim value assume(value i)
{
    picosat_assume(Int_val(i));
    return Val_unit;
}

/*------------------------------------------------------------------------*/
/* Call the main SAT routine.  A negative decision limits sets no limit on
 * the number of decisions.  The return values are as above, e.g.
 * 'PICOSAT_UNSATISFIABLE', 'PICOSAT_SATISFIABLE', or 'PICOSAT_UNKNOWN'.
 */
CAMLprim value sat(value limit)
{
    return Val_int(picosat_sat(Int_val(limit)));
}

/* After 'picosat_sat' was called and returned 'PICOSAT_SATISFIABLE', then
 * the satisfying assignment can be obtained by 'dereferencing' literals.
 * The value of the literal is return as '1' for 'true',  '-1' for 'false'
 * and '0' for an unknown value.
 */
CAMLprim value deref(value lit)
{
    return Val_int(picosat_deref(Int_val(lit)));
}

/* A cheap way of determining an over-approximation of a variable core is to
 * mark those variable that were resolved in deriving learned clauses.  This
 * can be done without keeping the proof trace in memory and thus does
 * not require to call 'picosat_enable_trace_generation' after
 * 'picosat_init'.
 */
CAMLprim value usedlit(value lit)
{
    return Val_int(picosat_usedlit(Int_val(lit)));
}

/*------------------------------------------------------------------------*/
/* The following five functions internally extract the variable and clausal
 * core and thus require trace generation to be enabled with
 * 'picosat_enable_trace_generation' right after calling 'picosat_init'.
 *
 * TODO: most likely none of them works for failed assumptions.  Therefore
 * trace generation currently makes only sense for non incremental usage.
 */

/* This function gives access to the variable core, which is made up of the
 * variables that were resolved in deriving the empty clauses.
 */
CAMLprim value corelit(value lit)
{
    return Val_int(picosat_corelit(Int_val(lit)));
}

//#include <stdio.h>

//CAMLprim value end_of_proof(){ return Val_int(EOP);}
value get_proof(value unit)
{
    CAMLparam0();
    CAMLlocal1 (array);
    int* proof = picosat_get_proof();
    int size = 0;
    while(proof[size] != EOP){
        size++;
    }
    //printf("EOP is: %i\n", EOP);
    //printf("proof has size: %i\n", size);
    array = caml_alloc_tuple(size);
    int i;
    for(i = 0; i < size; ++i){
        Store_field(array, i, Val_int(proof[i]));
    }
    CAMLreturn (array);
}

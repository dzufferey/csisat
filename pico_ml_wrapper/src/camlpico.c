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

#include<caml/mlvalues.h>
#include<caml/alloc.h>
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
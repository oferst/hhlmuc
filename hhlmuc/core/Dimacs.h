/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"
#include "core/MinimalCore.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B, class Solver>
static void readClause(B& in, Solver& S, int& icNum, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    skipWhitespace(in);
    assert(*in == '{');
    ++in;
    icNum = parseInt(in);
    ++in;
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

template<class B>
static void parse_DIMACS_main(B& in, CMinimalCore& core) {
    SimpSolver& S = core.GetSolver();
    vec<Lit> lits;
    int vars    = 0;
    uint32_t clauses = 0;
    uint32_t ics = 0;
    uint32_t cnt     = 0;
    uint32_t uid     = UINT32_MAX;
    int nIcNum = 0;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p gcnf")){
                vars    = parseInt(in);
                clauses = parseInt(in);
                ics = parseInt(in);
                core.SetICNum(ics);
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("c PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            cnt++;
            readClause(in, S, nIcNum, lits);

            if (nIcNum > 0)
            {
                if (core.m_bIcInConfl)
                {
                    continue;
                }

                S.addClause_(lits, true);
                if (uid != Clause::GetLastUid())
                {
                    uid = Clause::GetLastUid();
                    core.SetUidToIcs(uid, nIcNum - 1);
                }
                else
                {
                    if (!S.okay())
                    {
                        assert(uid == Clause::GetLastUid());
                        Clause::IncreaseUid();
                        S.CreateResolVertex(++uid);
                        S.AddConflictingIc(uid);
                        core.SetUidToIcs(uid, nIcNum - 1);
                        core.m_bIcInConfl = true;
                    }
                }
            }
            else
                S.addClause_(lits, false); 
        }
    }
    if (vars != S.nVars())
        fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
    if (cnt  != clauses)
        fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
}


// Inserts problem into solver.
//
static void parse_DIMACS(gzFile input_stream, CMinimalCore& core) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, core); }

//=================================================================================================
}

#endif

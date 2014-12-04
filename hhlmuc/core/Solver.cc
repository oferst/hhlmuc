/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static BoolOption    opt_ic_simplify       (_cat, "ic-simplify", "If to perform conflict simplification using other ic\n", false);
static IntOption     opt_bind_as_orig      (_cat, "bind-as-orig", "Bind ic clauses that are in muc as originals 0 - no, 1 - only original 2 - all cone\n", 2, IntRange(0,2));
static BoolOption    opt_post_ic_imp       (_cat, "post-ic-imp", "Postpone ic implications\n", true);
static BoolOption    opt_ic_as_dec         (_cat, "ic-as-dec",  "Treat ics as decisions during conflict analysis\n", true);
static BoolOption    opt_full_bck          (_cat, "full-bck",  "If backtrack to the end of original confl or new\n", true);
static BoolOption    opt_dec_l1            (_cat, "dec-l1",  "If to decide l1 or l2 (where l1 is 1UIP of first analyze and l2 is 1UIP where ic as dec\n", true);
static BoolOption    opt_local_restart     (_cat, "local-restart", "Use local restart", false);
static BoolOption    opt_glucose           (_cat, "glucose", "If to use glucose deletion strategy", true);
static IntOption     opt_blocker		   (_cat, "blocker", "0 - blocker is a watch, 1 - blocker is a sat literal when possible, 2 - same as 1, but try to separate from watcher\n", 0, IntRange(0,2));

//=================================================================================================
// Constructor/Destructor:

uint32_t Clause::icUid = 0;

Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), num_blocked(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{
    vecConfl.push(0);
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


void Solver::CreateOccurs() {
	m_Occurs.growTo(nVars() * 2);
	for (int i = 0; i < clauses.size(); ++i) {
		CRef cref = clauses[i];
		Clause& cls = ca[cref];
		for (int j = 0; j < cls.size(); ++j) {
			int z = toInt(cls[j]);
			m_Occurs[z].push(cref);
		}
	}

	for (int i = 0; i < icUnitClauses.size(); ++i)
	{
		CRef ref = icUnitClauses[i];
		if (ref == CRef_Undef) continue; // not sure if this case possible
		Clause& cls = ca[ref];
		if (cls.mark() != 0 || cls.learnt()) continue; // we don't need removed or learnt unit clauses
		m_Occurs[toInt(cls[0])].push(ref);
	}
}

// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver::addClause_(vec<Lit>& ps, bool ic, vec<uint32_t>* parents)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    CRef cr;
    if (ps.size() == 0)
    {
        return ok = false;
    }
    if (ps.size() == 1){
        if (ic) 
        {
            cr = ca.alloc(ps, false, true);
            icUnitClauses.push(cr);
        }
        else
        {
            uncheckedEnqueue(ps[0]);
            return ok = (propagate() == CRef_Undef);
        }
    }else{
        cr = ca.alloc(ps, false, ic);
        clauses.push(cr);
        attachClause(cr);
    }

    if (ic)
    {
        resol.AddNewResolution(ca[cr].uid(), cr, (parents == NULL) ? icParents : *parents);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    if (c.size() > 1)
        detachClause(cr);
    // Don't leave pointers to freed memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    if (c.ic() && c.mark() != 2)
        resol.DeleteClause(c.uid());
    c.mark(1); 
    ca.free(cr);

}

bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }

bool Solver::model_satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (modelValue(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        vecConfl.shrink(trail_lim.size() - level);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, vec<uint32_t>& icParents)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt() && !opt_glucose)
            claBumpActivity(c);

        if (c.ic())
        {
            icParents.push(c.uid());
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));

                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){ // conflict clause minimization: deep
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level, icParents))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){ // conflict clause minimization: basic
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels, vec<uint32_t>& icParents)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    int icTop = icParents.size();
    while (analyze_stack.size() > 0){
        Var v = var(analyze_stack.last());
        assert(reason(v) != CRef_Undef);
        Clause& c = ca[reason(v)]; analyze_stack.pop();
        if (!opt_ic_simplify && c.ic())
        {
            for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
            analyze_toclear.shrink(analyze_toclear.size() - top);
            icParents.shrink(icParents.size() - icTop);
            return false;
        }
        else if (c.ic())
        {
            icParents.push(c.uid());
        }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    icParents.shrink(icParents.size() - icTop);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


bool Solver::get_watch(Clause&  c, Watcher& w, Lit& false_lit) {
	if (opt_blocker	== 0) {  // original 
		for (int k = 2; k < c.size(); k++) {
			Lit lk = c[k];
			if (value(lk) != l_False) {  // found a watch
				c[1] = lk; c[k] = false_lit;										
				watches[~c[1]].push(w);

				return true; // that's the only case that watch_index_new is not promoted, i.e., w will not be watched by p.
			}
		}
	}
	
	else  {
		int newWatch = 0, newBlocker = 0;
		for (int k = 2; k < c.size(); k++) {
			lbool val = value(c[k]);
			if (opt_blocker == 1)	{  // blocker will be different than watch only if the pattern is undef ... sat ... 
				if (newBlocker == 0 && val == l_True) newBlocker = k; 
				if (newWatch == 0 && val != l_False) newWatch = k; 						
			}
			else {  // blocker will be different than watch if possible. 
				if (newWatch == 0 && val != l_False) newWatch = k; 
				else if (newBlocker == 0 && val == l_True) newBlocker = k; 	// the else forces blocker to be a different literal if possible					
			}
			if (newBlocker && newWatch) break;
		}					
		if (newWatch && !newBlocker) newBlocker = newWatch;
		if (newWatch > 0) {
			c[1] = c[newWatch]; c[newWatch] = false_lit;
			if (newBlocker) w.blocker = c[newBlocker]; 
			watches[~c[1]].push(w);
			return true; // that's the only case that watch_index_new is not promoted, i.e., w will not be watched by p.
		}
	}
	//////////////////////////////////////////////////////////////////////////
	return false;
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/


CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;	
    watches.cleanAll();
    icImpl.clear();
    int icImplId = 0;

    for (;;) 
    {
        while (qhead < trail.size()) {
            Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
            vec<Watcher>&  ws  = watches[p];
            Watcher        *watch_index_old, *watch_index_new, *end; // watch_index_old = index into existing watch list; watch_index_old  = index into a watch-list constructed during this loop. It will be smaller or equal to watch_index_old; watch_index_old and watch_index_new point to the same list, but watch_index_new may progress slower and overrun the data; Eventually the excess clauses are removed via shrink().
            num_props++;

            for (watch_index_old = watch_index_new = (Watcher*)ws, end = watch_index_old + ws.size();  watch_index_old != end;){
                // Try to avoid inspecting the clause:
                Lit blocker = watch_index_old->blocker;
                if (value(blocker) == l_True) {
                    *watch_index_new++ = *watch_index_old++; 
					num_blocked++;
					continue; 
				}

                // Make sure the false literal is data[1]:
                CRef     cr        = watch_index_old->cref;
                Clause&  c         = ca[cr];
				//c.print_dimacs();
                Lit      false_lit = ~p;
                if (c[0] == false_lit)
                    c[0] = c[1], c[1] = false_lit;				
                assert(c[1] == false_lit);
                watch_index_old++;

                // If 0th watch is true, then clause is already satisfied.
                Lit     first = c[0];
                Watcher w     = Watcher(cr, first);
                if (first != blocker && value(first) == l_True) {
                    *watch_index_new++ = w; 					
					continue; 
				}
            
							
			   if (get_watch(c, w, false_lit)) goto NextClause;
							

                // Did not find watch -- clause is either in conflict or is unit under assignment:
                *watch_index_new++ = w;
                if (value(first) == l_False) {  // a conflict found
                        confl = cr;
                        qhead = trail.size(); // will take us out of the while loop
                        // Copy the remaining watches:
                        while (watch_index_old < end) 
                            *watch_index_new++ = *watch_index_old++;
                }
                else  // unit
                {
                    if (decisionLevel() == 0 && c.ic()) {  // c becomes unit at decision level 0. So we can erase it (temporarily) and replace it with the unit. For non-ic clauses this is done in normal preprocessing (??)
                        add_tmp.clear();
                        add_tmp.push(first);
                        CRef newCr = ca.alloc(add_tmp, false, true);
						Clause& c = ca[cr];   // ?? why redefine c 
                        Clause::DecreaseUid();
                        ca[newCr].uid() = c.uid();
                        c.mark(2);
                        removeClause(cr);
                        resol.UpdateInd(c.uid(), newCr);
                        icUnitClauses.push(newCr);
						if (m_Occurs.size() > 0) 
							m_Occurs[toInt(first)].push(newCr);
                    }
                    else
                    {
                        if (opt_post_ic_imp && c.ic())  // postpone ic implications
                        {
                            icImpl.push();
                            Map<Lit, CRef>::Pair& pair = icImpl.last();
                            pair.key = first;
                            pair.data = cr;
                        }
                        else
                        {
                            uncheckedEnqueue(first, cr);   // normal propagation: making the assignment, adding to the trail
                        }
                    }
                }

            NextClause:;
            }
            ws.shrink(watch_index_old - watch_index_new);
        }
		
		if (confl != CRef_Undef) break;
		if (icImplId == icImpl.size()) break;
		
		while (icImplId != icImpl.size())
		{
			Map<Lit, CRef>::Pair& pair = icImpl[icImplId++];
			if (value(pair.key) == l_Undef)
			{
				uncheckedEnqueue(pair.key, pair.data);
				break;
			}
			else if (value(pair.key) == l_False)
			{
				confl = pair.data;
				break;
			}
		}
		
    } // for(;;)

    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}





/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        // First criteria 
        if (ca[x].size() == 2) return false;
        if (ca[y].size() == 2) return true;

        // Second one
        if (opt_glucose)
        {
            if (ca[x].activity() == ca[y].activity())
                return ca[x].size() < ca[y].size();

            return (ca[x].activity() > ca[y].activity());
        }
        else
            return (ca[x].activity() < ca[y].activity());
    }};
    
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.mark() == 0 && c.size() > 2 && !locked(c) && 
            ((!opt_glucose && (i < learnts.size() / 2 || c.activity() < extra_lim)) ||
            (opt_glucose && i < learnts.size() / 2 && c.activity() > 2)))
            removeClause(learnts[i]);
        else
            if (c.mark() != 1)
                learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
    resol.CheckGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.mark() == 1)
            continue;
        if (satisfied(c))
        {
            c.mark(0);
            removeClause(cs[i]);
        }
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assignment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    removeSatisfied(icUnitClauses);
    checkGarbage();
    resol.CheckGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assignment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;
    CRef confl = CRef_Undef;
    icParents.clear();

    for (;;){
        if (asynch_interrupt)
            return l_Undef;
        if (decisionLevel() == 0)
        {
            // Simplify the set of problem clauses:
            if (!simplify())
                return l_False;
            newDecisionLevel(conflictC);
            for (int nInd = 0; nInd < icUnitClauses.size(); ++nInd)
            {
                Clause& c = ca[icUnitClauses[nInd]];
                if (c.mark() != 0)
                    continue;
                Lit lit = c[0];
                if (value(lit) == l_False)
                {
                    confl = icUnitClauses[nInd];
                    break;
                }
                else if (value(lit) == l_True)
                {
                    continue;
                }

                uncheckedEnqueue(lit, icUnitClauses[nInd]);
                confl = propagate();
                if (confl != CRef_Undef)
                    break;
            }
        }

        if (confl == CRef_Undef)
            confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 1)
            {
                CreateUnsatCore(confl);
                return l_False;
            }

            if (decisionLevel() == 0) 
                return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, icParents);

			if (opt_ic_as_dec && learnt_clause.size() > 1 && icParents.size() > 0 && !ca[confl].ic()) // optimization "E". 
			{
				int index = trail.size() - 1;
				Lit l = trail[index];
				int dLevel = decisionLevel() + 1;
				// create a new decision level till ic clause
				while(!ca[reason(var(l))].ic())
				{
					// now we are going to learn a new 
					vardata[var(l)].level = dLevel;
					l = trail[--index];
				}

				vardata[var(l)].level = dLevel;
				vardata[var(l)].reason = CRef_Undef;
				trail_lim.push(index);
				vecConfl.push(conflictC);
				l = learnt_clause[0];
				learnt_clause.clear();
				int bckTrack = 0;
				analyze(confl, learnt_clause, bckTrack, icParents);
				CRef cr = ca.alloc(learnt_clause, true, false);
				learnts.push(cr);
				attachClause(cr);
				if (!opt_glucose)
					claBumpActivity(ca[cr]);
				else
					ca[cr].activity() = calculateDecisionLevels(learnt_clause);
				cancelUntil(opt_full_bck ? backtrack_level : dLevel-2);
				newDecisionLevel(conflictC);
				uncheckedEnqueue(opt_dec_l1 ? l : learnt_clause[0]);
			}
			else
			{
				if (learnt_clause.size() == 1)
				{
					if (icParents.size() > 0)
					{
						cancelUntil(1);
						CRef cr = ca.alloc(learnt_clause, false, true);
						icUnitClauses.push(cr);
						resol.AddNewResolution(ca[cr].uid(), cr, icParents);
						uncheckedEnqueue(learnt_clause[0], cr);
					}
					else
					{
						assert(backtrack_level == 0);
						cancelUntil(0);
						uncheckedEnqueue(learnt_clause[0]);
					}
				}
				else
				{
					cancelUntil(backtrack_level);
					CRef cr = ca.alloc(learnt_clause, true, icParents.size() > 0);
					learnts.push(cr);
					attachClause(cr);
					Clause& cl = ca[cr];
					if (!opt_glucose)
						claBumpActivity(ca[cr]);
					else
						ca[cr].activity() = calculateDecisionLevels(learnt_clause);
					if (cl.ic())
					{
						resol.AddNewResolution(cl.uid(), cr, icParents);
					}

					uncheckedEnqueue(learnt_clause[0], cr);
					//                fprintf(flog, "b - %d :", backtrack_level);
					//                printClause(flog, ca[cr]);
				}
			}

            varDecayActivity();
            if (!opt_glucose)
                claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

            icParents.clear();
            confl = CRef_Undef;

        } // end of dealing with a conflict
        else {
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts &&
                (!opt_local_restart || (conflictC - vecConfl[decisionLevel()]) >= nof_conflicts) || 
                !withinBudget()) 
            {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(1);
                return l_Undef; 
            }

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
/*
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }
*/

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();
//                fprintf(flog, "d - %d\n", var(next)+1);

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel(conflictC);
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;
    decLevInConfl.growTo(nVars(), 0);

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
//        fprintf(flog, "Starts %d\n", curr_restarts);
        status = search(rest_base * restart_first);
        if (asynch_interrupt && status == l_Undef)
            return l_Undef;
//        fflush(flog);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("c ===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    } 

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }
    
    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++) 
    {
        ca.reloc(learnts[i], to);
        Clause& c = to[learnts[i]];
        if (c.ic())
           resol.UpdateInd(c.uid(), learnts[i]);
    }

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
    {
        ca.reloc(clauses[i], to);
        Clause& c = to[clauses[i]];
        if (c.ic())
            resol.UpdateInd(c.uid(), clauses[i]);
    }

    for (int i = 0; i < icUnitClauses.size(); i++)
    {
        ca.reloc(icUnitClauses[i], to);
        Clause& c = to[icUnitClauses[i]];
        assert(c.ic());
        resol.UpdateInd(c.uid(), icUnitClauses[i]);
    }

	for(int i = 0; i < m_Occurs.size(); ++i) {
		vec<CRef>& tmpvec = m_Occurs[i];
		int j = 0;
		int newidx = 0;
		bool weHaveDeletions = false;	
		for (; j < tmpvec.size(); ++j) {
			if (ca[tmpvec[j]].mark() == 1) { // was deleted			
				weHaveDeletions = true; 
				continue;
			} 
			ca.reloc(tmpvec[j], to); // tmpvec[j] is sent by reference. It is updated with the new CRef (the index of the clause) if that clause was moved in memory. 'to' is the new database.
			if (weHaveDeletions) 
				tmpvec[newidx] = tmpvec[j];
			newidx++;
		}
		if (weHaveDeletions) 
			tmpvec.shrink(j - newidx); // removes those many elements from the end. 
	}
}

void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void Solver::CreateUnsatCore(CRef ref)
{
    if (decisionLevel() == 0)
        return;

    CRef confl = ref;
    int index   = trail.size() - 1;
    Var v = var_Undef;
    int nSeen = 0;

    for (;;) 
    {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.ic())
            icParents.push(c.uid());

        for (int j = (v == var_Undef) ? 0 : 1 ; j < c.size(); j++)
        {
            v = var(c[j]);
            assert(value(c[j]) == l_False);

            if (!seen[v] && level(v) > 0)
            {
                seen[v] = 1;
                ++nSeen;
            }
        }

        if (nSeen == 0)
            break;
        
        // Select next clause to look at:		
        while (!seen[var(trail[index--])]);
        v     = var(trail[index+1]);
        confl = reason(v);
        seen[v] = 0;
        --nSeen;
    }
}

void Solver::GetUnsatCore(vec<uint32_t>& core)
{
    core.clear();
    Set<uint32_t> set;
    for (int nInd = 0; nInd < icParents.size(); ++nInd)
    {
        if (set.insert(icParents[nInd]))
            resol.GetOriginalParentsUids(icParents[nInd], core, set);
    }
}

void Solver::RemoveClauses(vec<uint32_t>& cone)
{
    resol.GetClausesCones(cone);
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            ca[cr].mark(0);
            removeClause(cr);
        }
    }

    // check that all the clauses are actually removed
/*    for (int i = 0; i < cone.size(); ++i)
    {
        assert (resol.GetInd(cone[i]) == CRef_Undef);
        assert(resol.GetResolId(cone[i]) == CRef_Undef);
    }
*/
}



void Solver::MarkClauses(vec<uint32_t>& cone, int mark)  // what is sent here are root clauses, not cone. 
{
	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resol.GetInd(cone[i]);
		if (cr != CRef_Undef)
		{
			Clause& c = ca[cr];
			if (c.size() > 1)
				c.mark(mark);
		}
	}

}


// removes watches from input clauses + their cone. 
void Solver::UnbindClauses(vec<uint32_t>& cone)  // what is sent here are root clauses, not cone. 
{
    resol.GetClausesCones(cone);  // now we add to the input clause-set of roots, their cones (incl. clauses that have antecedents outside the set of roots). 
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
            if (c.size() > 1)
            {
                detachClause(cr);
                // so we will be able to use lazy watch removal
                c.mark(1); 
            }
            else
            {
                c.mark(2);
            }
        }
    }

    watches.cleanAll();  // removes watches. 

    for (int i = 0; i < cone.size(); ++i)  // we mark them with 0 because we do not want them to be erased later. 
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
            if (c.size() > 1)
                c.mark(0);
        }
    }

}

void Solver::BindClauses(vec<uint32_t>& cone)  // 'cone' here is actually root ICs.
{
    if (opt_bind_as_orig == 2)  // optimization: add also the clauses in the cone of the roots as remainders.
    {
        resol.GetAllIcUids(setGood, cone);   // Updates setGood (see definition of setGood in the declaration).
    }

    resol.GetClausesCones(cone);
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resol.GetInd(uid);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
            
			// optimization: return IC clauses that are known to be in the HLMUC as remainder clauses
            if ((opt_bind_as_orig == 1 && resol.GetParentsNumber(uid) == 0) ||   // original clauses 
                (opt_bind_as_orig == 2 && setGood.has(uid)))            // learnt clauses that do not have an antecedent IC outside the input roots
			{
				c.mark(0);			
                removeClause(cr);
                analyze_stack.clear();

                bool satClause = false;
                for (int litId = 0; litId < c.size(); ++litId)
                {
                    if (value(c[litId]) == l_True)
                    {
                        satClause = true;
                        break;
                    }
                    else if (value(c[litId]) == l_False)
                    {
                        continue;
                    }
                    analyze_stack.push(c[litId]);
                }

                if (satClause)
                    continue;

                if (analyze_stack.size() == 0)
                {
                    ok = false;
                    return;
                }

                if (analyze_stack.size() == 1)
                {
                    enqueue(analyze_stack[0]);
                }
                else
                {
                    CRef newCr = ca.alloc(analyze_stack, c.learnt(), false); // false means that it is not IC. 
                    clauses.push(newCr);
                    attachClause(newCr);
					for (int i = 0; i < analyze_stack.size(); ++i)
					{
						// we can replace it here with the old version to save memory but pay the price for the speed
						m_Occurs[toInt(analyze_stack[i])].push(newCr);
					}

                }
            }
            else
            {
                if (c.size() > 1 && c.mark() == 2)  // when this function is called from Solve (the case the result was SAT), the clauses in vecUidsToRemove are marked with 2. 
                {
                    attachClause(cr);
                }

				c.mark(0);
            }
        }
    }
}

void Solver::printClause(FILE* f, Clause& c)
{
    for (int i = 0; i < c.size(); i++)
       fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", var(c[i])+1);
    fprintf(f, "0\n");
}

void Solver::CreateResolVertex(uint32_t uid)
{
    assert(icParents.size() == 0);
    resol.AddNewResolution(uid, CRef_Undef, icParents);
}

void Solver::AddConflictingIc(uint32_t uid)
{
    assert(icParents.size() == 0);
    icParents.push(uid);
    ok = true;
}

void Solver::ResetOk()
{
    ok = true;
}

int Solver::calculateDecisionLevels(vec<Lit>& cls)
{
    int decLevels = 0;
    for (int i=0; i<cls.size(); ++i )
    {
        int levelV = vardata[var(cls[i])].level;
        if (decLevInConfl[levelV] != conflicts)
        {
            ++decLevels;
            decLevInConfl[levelV] = conflicts;
        }
    }

    return decLevels;
}


void Solver::print_unsat_clauses() {		
	printf("The following clauses are unsat:\n");
	for (int i = 0; i < clauses.size(); ++i) {
		Clause& cl = ca[clauses[i]];
		if (cl.mark() != 0) continue;
		if (!model_satisfied(cl)) {
			printf("uid = %d ", cl.ic() ? cl.uid() : -1);
			printClause(stdout, cl);				
		}
	}

	for (int i = 0; i < icUnitClauses.size(); ++i)
	{
		CRef ref = icUnitClauses[i];
		if (ref == CRef_Undef) continue; // not sure if this case possible
		Clause& cl = ca[ref];
		if (cl.mark() != 0 || cl.learnt()) continue; // we don't need removed or learnt unit clauses
		if (!model_satisfied(cl)) {
			printf("uid = %d ", cl.uid());
			printClause(stdout, cl);				
		}
	}
		printf("\n");

}


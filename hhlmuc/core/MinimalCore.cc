#include "core/MinimalCore.h"
#include "utils/ParseUtils.h"
#include "mtl/Sort.h"
#include "utils/System.h"
#include "mtl/Alg.h"
#include <stdio.h>
#include <assert.h>

namespace Minisat
{
	static const char* _cat = "HLMUC";
	static IntOption  remove_order(_cat, "remove-order", "Which order to remove: 0 - from largest, 1 - smallest, 2 - highest, 3 - lowest\n", 0, IntRange(0, 3));
	static BoolOption opt_muc_rotate (_cat, "rotate", "perform rotation", true);

	CMinimalCore::CMinimalCore(SimpSolver& solver):
		m_bIcInConfl(false)
		, m_UidToIC()
		, m_IcToUids()
		, m_Solver(solver)
		, m_nICSize(0)
		, m_nRotationCalled(0)
		, m_nRotationFirstCalls(0)
		, m_nRotationICsAdded(0)
	{}

	void CMinimalCore::SetICNum(uint32_t nIcNum)
	{
		m_nICSize = nIcNum;
		m_IcToUids.growTo(m_nICSize);
	}

	void CMinimalCore::SetUidToIcs(uint32_t nClsUid, uint32_t nIc)
	{
		m_UidToIC.growTo(nClsUid + 1);
		m_UidToIC[nClsUid] = nIc;
		m_IcToUids[nIc].push(nClsUid);
	}

	void CMinimalCore::PrintData(int unknownSize, int mucSize, int iter, int rotation, bool last)
	{
		printf("c %siter %d time %g not-muc %d unknown %d muc %d  (rotation added %d ICs)\n", 
			last ? "final " : "", 
			iter + 1, 
			cpuTime(),
			m_nICSize - mucSize - unknownSize, 
			unknownSize, 
			mucSize, 
			rotation);
	}

	// Doxygen-friendly comments... 
	/** Model rotation. Finds additional ICs to add to the HLMUC. 	
	*/	
	void CMinimalCore::Rotate(
		uint32_t IC_id, /**< An id of an interesting constraint, without which the formula is SAT.  */
		Var v, /**< the variable we flip its value. This helps avoiding cycles. */
		Set<uint32_t>& moreMucClauses, /**<will be filled with additional ICs*/ 
		Set<uint32_t>& setHLMuc, /**< current core. */
		bool bUseSet /**< true <=> call recursively even if the IC is already in the core. 	*/
		)
	{
		int i;
		++m_nRotationCalled;    		
		
		// finding the intersection of all unsat clauses
		vec<uint32_t>& clauses_vec =  m_IcToUids[IC_id];
		vec<Lit> intersec, tmpvec1, tmpvec2;
		CRef ref;
		for (i = 0; i < clauses_vec.size(); ++i) {  // searching for the first unsat clause
			ref = m_Solver.GetClauseIndFromUid(clauses_vec[i]);
			if (ref == CRef_Undef) continue;
			if (!m_Solver.model_satisfied(m_Solver.GetClause(ref))) break;
		}
		assert(i < clauses_vec.size()); // if this assertion breaks, it means that all clauses in IC are sat, which is supposed to be impossible. 
				
		Clause& clause = m_Solver.GetClause(ref); // m_Solver.GetClauseFromUid(clauses_vec[i]);

		clause.copyTo(intersec);
		sort(intersec);		
		for (++i; i < clauses_vec.size(); ++i) {  
			ref = m_Solver.GetClauseIndFromUid(clauses_vec[i]);
			if (ref == CRef_Undef) continue;
			Clause& clause = m_Solver.GetClause(ref); 
			if (m_Solver.model_satisfied(clause)) continue;			
			clause.copyTo(tmpvec2);
			sort(tmpvec2);
			intersec.swap(tmpvec1);
			intersec.clear();
			Intersection(tmpvec1, tmpvec2, intersec);
		}		

		// at this point intersec contains the literals in the intersection of all unsat clauses. Flipping each of them, by definition, satisfies the clauses in IC_id.
		
		for (i = 0; i < intersec.size(); ++i)
		{
			// we will pass one by one literal and check if the clause is satisfiable with change 
			Lit lit = intersec[i];
			int unsat_IC =   -1;
			Var checkVar = var(lit);			
			if ((checkVar == v) || (m_Solver.level(checkVar) == 0)) {			
				continue;
			}

			// first we swap v in the model and count the number of ICs that became unsat as a result of it
			assert(m_Solver.modelValue(lit) == l_False);			
			m_Solver.model[checkVar] = m_Solver.model[checkVar] ^ 1;  // swapping value
			vec<CRef>& _cs = m_Solver.m_Occurs[toInt(~lit)]; 			
			
			unsigned unsat_cls_counter = 0;
			bool found_one_unsat_IC = true;
			uint32_t unsatIC_id = CRef_Undef;        
			for (int j = 0; j < _cs.size(); ++j)  // going over clauses in the occur list of lit
			{            
				CRef ref = _cs[j];			
				if  (ref == CRef_Undef) // previously removed
					continue;
				Clause& cls = m_Solver.GetClause(ref);
				if (cls.mark() != 0) continue;
				
				if (m_Solver.model_satisfied(cls)) continue; 			
				++unsat_cls_counter;
				if (!cls.ic()) {found_one_unsat_IC  = false; break;} // cls is in remainder and became unsat; hence we cannot continue with this literal. (TODO: we actually can if we call rotation recursively with remainder). 			
				unsigned current_ic = m_UidToIC[cls.uid()];
				if (current_ic == IC_id) {found_one_unsat_IC  = false; break;}
				if (current_ic == unsatIC_id) continue;  
				if (unsatIC_id != CRef_Undef) {found_one_unsat_IC  = false; break;}  // this is the second IC to be unsat; hence abondon this literal;
				unsatIC_id = current_ic;			
			}
			

			if (unsat_cls_counter == 0) 
			{
				assert(false); // at least one other IC has to become unsat (otherwise the formula with the IC is SAT, and we know it is unsat). 
				exit(0);
			}

			if (found_one_unsat_IC) 
			{
				if (bUseSet) // Continue even if we discovered an IC clause that is already in the core. 
				{
					if (!setHLMuc.has(unsatIC_id) && moreMucClauses.insert(unsatIC_id))
					{			
						Rotate(unsatIC_id, checkVar, moreMucClauses, setHLMuc, bUseSet);			
					}
				}
				else
				{
					if (moreMucClauses.insert(unsatIC_id))
					{
						Rotate(unsatIC_id, checkVar, moreMucClauses, setHLMuc, bUseSet);
					}
				}
			}			

			m_Solver.model[checkVar] = m_Solver.model[checkVar] ^ 1; // swap the value back to what it was before			
		} // end of for loop going over literals in the intersection. 
	}


	lbool CMinimalCore::Solve(bool pre)
	{
		vec<uint32_t> vecUnknown;
		vec<uint32_t> vecPrevUnknown;
		vec<uint32_t> vecUids;
		vec<Lit> dummy;
		uint32_t nIcForRemove = 0;
		vec<uint32_t> vecUidsToRemove;  // temporary vector of clause IDs. Stores the clauses of the IC that we are removing. 	
		Set<uint32_t> moreMucICs; 
		vec<uint32_t> moreMucICs_Vec;  // temporary vector to hold the value of the set moreMucICs. Technicality; because set does not have an iterator.  
		lbool result = l_Undef;
		Set<uint32_t> setHLMuc;
		Map<uint32_t, uint32_t> mapIcToScore;
		//    Set<uint32_t> setNotMuc;
		//    m_Solver.nIcNum = m_nICSize;

		// run preprocessing
		double before_time = cpuTime();
		if (!m_bIcInConfl)
			m_bIcInConfl = !m_Solver.eliminate(pre);
		double simplified_time = cpuTime();
		if (m_Solver.verbosity > 0)
		{
			printf("c |  Simplification time:  %12.2f s                                       |\n", simplified_time - before_time);
			printf("c |                                                                             |\n"); 
		}

		int nIteration = 0;
		for (; true; ++nIteration)
		{
			if (!m_bIcInConfl)
				result = ((Solver*)&m_Solver)->solveLimited(dummy);
			else
			{
				result = l_False;
				m_bIcInConfl = false;
				m_Solver.ResetOk();
			}
			if (result == l_False)
			{
				mapIcToScore.clear();				
				m_Solver.GetUnsatCore(vecUids); // get all the clauses in unsat core
				//vecUids.removeDuplicated_();
				// for each clause in vecUids check if its ic and mark it as unknown. 
				for (int nInd = 0; nInd < vecUids.size(); ++nInd)
				{
					assert(m_UidToIC.size() > vecUids[nInd]);					
					uint32_t nIc = m_UidToIC[vecUids[nInd]];
					if (!setHLMuc.has(nIc))
					{
						vecUnknown.push(nIc);
						if (remove_order < 2)
						{
							if (mapIcToScore.has(nIc))
								++mapIcToScore[nIc]; // counts the number of clauses in the cone that are in that ic. This will be used for the removal order heuristic. 
							else
							{
								mapIcToScore.insert(nIc, 1);								
							}
						}
					}
				}
				
				vecUnknown.removeDuplicated_();				

				PrintData(vecUnknown.size(), setHLMuc.elems(), nIteration, m_nRotationICsAdded);

				if (vecUnknown.size() == 0)
				{
					break;
				}

				// Now remove all unused ics and all their clauses.
				// For the first iteration all ics are inside so this needs a different treatment; for all others we will check the previous vector.

				// build backward resolution relation so it will be much easier to remove cones
				
				assert (nIteration == 0 ||  (vecUnknown.size() < vecPrevUnknown.size()));  // progress must have happened (is sat we moved at least one to HLMUC, if unsat we removed at least one outside).
												
				int nIndUnknown = 0;
				int nSize = nIteration == 0 ? m_nICSize : vecPrevUnknown.size();
				vecUidsToRemove.clear();
				for (int nInd = 0; nInd < nSize; ++nInd)
				{
					uint32_t nIcId = nIteration == 0 ? nInd : vecPrevUnknown[nInd];
					if (nIcId != vecUnknown[nIndUnknown])
					{												
						m_IcToUids[nIcId].addTo(vecUidsToRemove);	// get all the clauses that are related to this ic					
					}
					else
					{
						if (nIndUnknown + 1 < vecUnknown.size())
						{
							++nIndUnknown;
						}
					}
				}
				// remove their cones
				m_Solver.RemoveClauses(vecUidsToRemove);
				if (nIteration == 0) m_Solver.CreateOccurs();
			}
			else if (result == l_True)
			{
				if (nIteration == 0)
				{					
					return result; // the problem is sat
				}
				
				if (vecPrevUnknown.size() == 1) // only one left in the unknown, so if it is SAT then we are done. 
				{
					setHLMuc.insert(nIcForRemove);  // the IC must be in the core					
					result = l_False;
					break;
				}

				moreMucICs.clear();
				moreMucICs.insert(nIcForRemove);

				if (opt_muc_rotate)
				{
					++m_nRotationFirstCalls;
//					printf("Calling rotation\n=================\n");					
					Rotate(nIcForRemove, var_Undef, moreMucICs, setHLMuc, false/*((opt_set_ratio * setMuc.elems()) >= vecPrevUnknown.size())*/); // updates moreMucICs					
				}

				m_Solver.MarkClauses(vecUidsToRemove, 2);  // this marking is used later in BindClauses. 
				vecUidsToRemove.clear();
				moreMucICs_Vec.clear();
				moreMucICs.copyTo(moreMucICs_Vec);

				for (int i = 0; i < moreMucICs_Vec.size(); ++i)  // adds the clauses of all the ICs in moreMucVec into vecUidsToRemove; also inserts the ICs into setMuc
				{
					uint32_t IC_id = moreMucICs_Vec[i];
					if (setHLMuc.insert(IC_id))  // returns false if it is already there. 
					{
						if (IC_id != nIcForRemove) {
							++m_nRotationICsAdded;
							mapIcToScore.remove(IC_id);  // conditioned because we already removed (from mapIcToScore) nICForRemove in the previous iteration. 
						}
						m_IcToUids[IC_id].addTo(vecUidsToRemove);
						remove(vecPrevUnknown, IC_id);						
					}
				}

				if (vecPrevUnknown.size() == 0)
				{
					result = l_False;
					break;
				}
								
				m_Solver.BindClauses(vecUidsToRemove);

				vecPrevUnknown.swap(vecUnknown);				
				PrintData(vecUnknown.size(), setHLMuc.elems(), nIteration, m_nRotationICsAdded);
				
			}
			else // interrupt
			{				
				if (nIteration != 0)
					vecPrevUnknown.swap(vecUnknown);
				else
				{
					vecUnknown.growTo(m_nICSize);
					for (uint32_t nInd = 0; nInd < m_nICSize; ++nInd)
					{
						vecUnknown[nInd] = nInd;
					}
				}
				break;
			}

			switch ((unsigned)remove_order)
			{
			case 0:
				nIcForRemove = GetMaxIc(mapIcToScore);
				mapIcToScore.remove(nIcForRemove);
				break;
			case 1:
				nIcForRemove = GetMinIc(mapIcToScore);
				mapIcToScore.remove(nIcForRemove);
				break;
			case 2:
				nIcForRemove = vecUnknown.last();
				break;
			case 3:
				nIcForRemove = vecUnknown[0];
				break;
			}			
			m_IcToUids[nIcForRemove].copyTo(vecUidsToRemove);
			m_Solver.UnbindClauses(vecUidsToRemove);
			vecPrevUnknown.swap(vecUnknown);
			vecUnknown.clear();
		}

		PrintData(vecUnknown.size(), setHLMuc.elems(), nIteration, m_nRotationICsAdded, true );
		vec<uint32_t> vecMuc;
		setHLMuc.copyTo(vecMuc);
		sort(vecMuc);

		printf("v ");
		for (int nInd = 0; nInd < vecUnknown.size(); ++nInd) // supposed to be different than 0 only on interrupt (?). 
		{
			printf("%d ", vecUnknown[nInd] + 1);
		}

		for (int nInd = 0; nInd < vecMuc.size(); ++nInd)
		{
			printf("%d ", vecMuc[nInd] + 1);
		}
		printf("0\n");

		printf("blocked = %d\n", m_Solver.get_num_blocked());
		return result;
	}

	uint32_t CMinimalCore::GetMaxIc(Map<uint32_t, uint32_t>& mapIcToScore)
	{
		uint32_t maxVal = 0;
		uint32_t maxInd = 0;
		for (int bucketId = 0; bucketId < mapIcToScore.bucket_count(); ++bucketId)
		{
			const vec<Map<uint32_t, uint32_t>::Pair>& bucket = mapIcToScore.bucket(bucketId);
			for (int elId = 0; elId < bucket.size(); ++elId)
			{
				const Map<uint32_t, uint32_t>::Pair& pair = bucket[elId];
				if (pair.data > maxVal)
				{
					maxVal = pair.data;
					maxInd = pair.key;
				}
			}
		}

		return maxInd;
	}

	uint32_t CMinimalCore::GetMinIc(Map<uint32_t, uint32_t>& mapIcToScore)
	{
		uint32_t minVal = UINT32_MAX;
		uint32_t minInd = UINT32_MAX;
		for (int bucketId = 0; bucketId < mapIcToScore.bucket_count(); ++bucketId)
		{
			const vec<Map<uint32_t, uint32_t>::Pair>& bucket = mapIcToScore.bucket(bucketId);
			for (int elId = 0; elId < bucket.size(); ++elId)
			{
				const Map<uint32_t, uint32_t>::Pair& pair = bucket[elId];
				if (pair.data < minVal)
				{
					minVal = pair.data;
					minInd = pair.key;
					if (minVal == 1)
						return minInd;
				}
			}
		}

		return minInd;
	}

}

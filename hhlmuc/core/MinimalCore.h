#ifndef MINIMAL_CORE_H
#define MINIMAL_CORE_H

#include "simp/SimpSolver.h"
#include "mtl/Map.h"

namespace Minisat 
{

class CMinimalCore
{
public:
    CMinimalCore(SimpSolver& solver);

    void SetUidToIcs(uint32_t nClsUid, uint32_t nIc);

    lbool Solve(bool pre);

    inline SimpSolver& GetSolver() { return m_Solver; }

    void SetICNum(uint32_t nIcNum);

    bool m_bIcInConfl;
private:
   void PrintData(int unknownSize, int mucSize, int iter, int rotation, bool last = false);
   void Rotate(uint32_t uid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet);
   uint32_t GetMaxIc(Map<uint32_t, uint32_t>& mapIcToScore);
   uint32_t GetMinIc(Map<uint32_t, uint32_t>& mapIcToScore);
    int m_nRotationCalled;
    int m_nRotationFirstCalls;
    int m_nRotationICsAdded;

    vec<uint32_t> m_UidToIC; // maps a clause ID to the IC that it belongs to. 
    vec<vec<uint32_t> > m_IcToUids;  // maps ID of Interesting Constraint (IC) to the clauses that it contains
    SimpSolver& m_Solver;
    uint32_t m_nICSize;
};

}

#endif

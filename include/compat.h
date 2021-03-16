/*-------------------------------------------------------------------------
 *
 * compat.h
 *  Interface for functionality that breaks between major PG versions
 *
 * Copyright (c) 2018, PipelineDB, Inc.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "catalog/objectaddress.h"
#include "executor/tuptable.h"
#include "nodes/execnodes.h"
#if (PG_VERSION_NUM < 120000)
	#include "nodes/relation.h"
#else
	#include "nodes/pathnodes.h"
#endif

#if (PG_VERSION_NUM < 110000)
	#define PIPELINE_COMPAT_INDEX_ATTR_BITMAP_ALL INDEX_ATTR_BITMAP_ALL
#elif  (PG_VERSION_NUM < 120000)
	#define PIPELINE_COMPAT_INDEX_ATTR_BITMAP_ALL INDEX_ATTR_BITMAP_HOT
#else
	#define PIPELINE_COMPAT_INDEX_ATTR_BITMAP_ALL INDEX_ATTR_BITMAP_ALL
#endif

extern bool CompatProcOidIsAgg(Oid oid);
extern void CompatAnalyzeVacuumStmt(VacuumStmt *stmt);

extern Relids CompatCalcNestLoopRequiredOuter(Path *outer, Path *inner);
extern void CompatPrepareEState(PlannedStmt *pstmt, EState *estate);

extern void
CompatExecTuplesHashPrepare(int numCols,Oid *eqOperators,
#if (PG_VERSION_NUM < 110000)
		FmgrInfo **eqFunctions,
#else
		Oid **eqFunctions,
#endif
		FmgrInfo **hashFunctions);

extern TupleHashTable
CompatBuildTupleHashTable(TupleDesc inputDesc,
					int numCols, AttrNumber *keyColIdx,
#if (PG_VERSION_NUM < 110000)
					FmgrInfo *eqfuncs,
#elif (PG_VERSION_NUM < 120000)
					Oid *eqfuncs,
#else
					Oid *eqfuncs,Oid *collations,
#endif
					FmgrInfo *hashfunctions,
					long nbuckets, Size additionalsize,
					MemoryContext tablecxt,
					MemoryContext tempcxt, bool use_variable_hash_iv);

extern char *CompatGetAttName(Oid relid, AttrNumber att);
extern void ComaptExecAssignResultTypeFromTL(PlanState *ps);


-- OIDs are finicky and PG is moving away from them
ALTER TABLE pipelinedb.cont_query SET WITHOUT OIDS;
ALTER TABLE pipelinedb.stream SET WITHOUT OIDS;

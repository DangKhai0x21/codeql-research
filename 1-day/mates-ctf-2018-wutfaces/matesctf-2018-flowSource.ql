/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph
import semmle.code.java.dataflow.FlowSources

class DecodeObjectData extends MethodAccess{
    DecodeObjectData(){
        this.getCallee().hasName("decodeObjectData")
    }
}

class ConfigureSS extends TaintTracking::Configuration{
    ConfigureSS(){this = "ConfigureSS"}
    override predicate isSource(DataFlow::Node source) {
        exists(RemoteFlowSource rfs |  source = rfs and
            rfs.getLocation().getFile().getRelativePath().matches("%/src/test/%"))
    }

    override predicate isSink(DataFlow::Node sink) {
        exists(DecodeObjectData dod | sink.asExpr() = dod.getArgument(0) and
        dod.getArgument(0).getType().hasName("String"))
    }
}
from ConfigureSS cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
    cfg.hasFlowPath(source, sink)
select sink,source,sink,"untrust data"
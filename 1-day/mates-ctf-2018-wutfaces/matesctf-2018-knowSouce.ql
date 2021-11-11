/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph


class HandleResourceRequest extends Method{
    HandleResourceRequest(){
        this.hasName("handleResourceRequest") and
        this.getDeclaringType().hasQualifiedName("org.richfaces.resource", "ResourceHandlerImpl")
    }
}

class DecodeObjectData extends MethodAccess{
    DecodeObjectData(){
        this.getCallee().hasName("decodeObjectData")
    }
}

class ConfigureSS extends TaintTracking::Configuration{
    ConfigureSS(){ this = "ConfigureSS" }
    override predicate isSource(DataFlow::Node source) {
        exists(HandleResourceRequest hrr | source.asParameter() = hrr.getParameter(0) )
    }
    override predicate isSink(DataFlow::Node sink) {
        exists(DecodeObjectData dod | sink.asExpr() = dod.getArgument(0) )
    }
}

from ConfigureSS cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
    cfg.hasFlowPath(source, sink)
select sink, source, sink, "untrust data"

// from DecodeObjectData dod
// select dod
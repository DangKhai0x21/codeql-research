/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PathGraph

class HandleResourceRequest extends Method{
    HandleResourceRequest(){
        this.hasName("handleResourceRequest") and
        this.getDeclaringType().hasQualifiedName("org.richfaces.resource", "ResourceHandlerImpl")
    }
}

class ReadObject extends MethodAccess{
    ReadObject(){
        this.getCallee().hasName("readObject") and
        this.getCaller().hasName("decodeObjectData")
    }
}

class DecodeResourceTaintStep extends TaintTracking::AdditionalTaintStep{
    override predicate step(DataFlow::Node pre, DataFlow::Node succ) {
        exists(MethodAccess ma | 
        pre.asExpr() = ma.getArgument(0) and
        succ.asExpr() = ma and
        ma.getCallee().hasName("decodeResource") and
        ma.getCaller().hasName("handleResourceRequest"))
    }
}


class DecodeBytesDataTaintStep extends TaintTracking::AdditionalTaintStep{
    override predicate step(DataFlow::Node pre,DataFlow::Node succ) {
        exists(MethodAccess ma| 
        pre.asExpr() = ma.getArgument(0) and
        succ.asExpr()= ma and
        ma.getCallee().hasName("decodeBytesData") and
        ma.getCaller().hasName("decodeObjectData"))
    }
}

class ResourceRequestDataFieldTaintStep extends TaintTracking::AdditionalTaintStep {
    override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
      DataFlow::getFieldQualifier(any(FieldAccess fa |
          fa = node2.asExpr() and
          fa.getField().getDeclaringType().getASupertype().hasName("ResourceRequestData")
        )) = node1
    }
  }


class ConfigureSS extends TaintTracking::Configuration{
    ConfigureSS(){ this = "ConfigureSS" }
    override predicate isSource(DataFlow::Node source) {
        exists(HandleResourceRequest hrr | source.asParameter() = hrr.getParameter(0) )
    }

    override predicate isSink(DataFlow::Node sink) {
            exists(ReadObject ro | sink.asExpr() = ro.getQualifier() )
        }
    override int explorationLimit() { result =  20} 
}

from ConfigureSS cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
    cfg.hasFlowPath(source, sink)
select sink, source, sink,"Untrust data" 



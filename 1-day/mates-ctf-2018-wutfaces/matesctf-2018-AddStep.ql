/**
 * @kind path-problem
 */

import java
import semmle.code.java.dataflow.TaintTracking
import DataFlow::PartialPathGraph

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

class AddStepTwo extends TaintTracking::AdditionalTaintStep{
    override predicate step(DataFlow::Node pre, DataFlow::Node succ) {
        exists(MethodAccess ma | 
        pre.asExpr() = ma.getArgument(0) and
        succ.asExpr() = ma and
        ma.getCallee().hasName("decodeResource") and
        ma.getCaller().hasName("handleResourceRequest"))
    }
}

// class AddStep3 extends TaintTracking::AdditionalTaintStep{
//     override predicate step(DataFlow::Node pre,DataFlow::Node succ) {
//         exists(MethodAccess ma|
//         pre.asExpr() = ma.getArgument(0) and
//         succ.asExpr() = ma and
//         ma.getQualifier().toString() = "Util" and
//         ma.getCallee().hasName("decodeObjectData") and
//         ma.getCaller().hasName("getData")
//         )
//     }
// }

class AddStep4 extends TaintTracking::AdditionalTaintStep{
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
          fa.getField().getDeclaringType().getASupertype*().hasName("ResourceRequestData")
        )) = node1
    }
  }


class AddStep5 extends TaintTracking::AdditionalTaintStep{
    override predicate step(DataFlow::Node pre,DataFlow::Node succ) {
        exists(ConstructorCall cc| 
        pre.asExpr() = cc.getArgument(0) and
        succ.asExpr()= cc and
        cc.getConstructor().hasName("ObjectInputStreamImpl")
        )
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

from ConfigureSS cfg, DataFlow::PartialPathNode source, DataFlow::PartialPathNode sink
where
    cfg.hasPartialFlow(source, sink, _)
select sink, source.getNode(), sink,"Partial flow from unsanitized user data " 



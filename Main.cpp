#include <iostream>
#include <stdlib.h>
#include <rose.h>
#include <CPPAstInterface.h>
#include <AstInterface_ROSE.h>
#include <ArrayRewrite.h>
#include <LoopTreeDepComp.h>
#include <OmpAttribute.h>
#include <OmpSupport.h>
#include <RoseAst.h>
#include "ompAstConstruction.h"

using namespace std;
using namespace SageInterface;
using namespace SageBuilder;
using namespace OmpSupport;

static SgStatement *firstStmt;
DFAnalysis * defuse = NULL;
LivenessAnalysis* liv = NULL;

bool enable_debug;
bool b_unique_indirect_index;


static std::map< std::string,std::pair< int , std::vector<int> > > storeDynArr;

bool initialize_analysis(SgProject* project,bool debug)
{
    if (project == NULL)
      project = SageInterface::getProject();
    // Prepare def-use analysis
    if (defuse==NULL)
    {
      ROSE_ASSERT(project != NULL);
      defuse = new DefUseAnalysis(project);
    }

    ROSE_ASSERT(defuse != NULL);
    // int result = ;
    defuse->run(debug);
    //  if (result==1)
    //    std::cerr<<"Error in Def-use analysis!"<<std::endl;
    if (debug)
      defuse->dfaToDOT();

    //Prepare variable liveness analysis
    if (liv == NULL)
      liv = new LivenessAnalysis(debug,(DefUseAnalysis*)defuse);
    ROSE_ASSERT(liv != NULL);

    std::vector <FilteredCFGNode < IsDFAFilter > > dfaFunctions;
    NodeQuerySynthesizedAttributeType vars=NodeQuery::querySubTree(project, V_SgFunctionDefinition);
    NodeQuerySynthesizedAttributeType::const_iterator i;
    bool abortme=false;
    // run liveness analysis on each function body
    for (i= vars.begin(); i!=vars.end();++i)
    {
      SgFunctionDefinition* func = isSgFunctionDefinition(*i);
      if (debug)
      {
        std::string name = func->class_name();
        std::string funcName = func->get_declaration()->get_qualified_name().str();
        std::cout<< " .. running liveness analysis for function: " << funcName << std::endl;
      }
      FilteredCFGNode <IsDFAFilter> rem_source = liv->run(func,abortme);
      if (rem_source.getNode()!=NULL)
        dfaFunctions.push_back(rem_source);
      if (abortme)
        break;
    } // end for ()
    if(debug)
    {
      std::cout << "Writing out liveness analysis results into var.dot... " << std::endl;
      std::ofstream f2("var.dot");
      dfaToDot(f2,std::string("var"), dfaFunctions, (DefUseAnalysis*)defuse, liv);
      f2.close();
    }
    if (abortme) {
      std::cerr<<"Error: Liveness analysis is ABORTING ." << std::endl;
      ROSE_ASSERT(false);
    }
    return !abortme;
} // end initialize_analysis()

void release_analysis()
{
    if(defuse!=NULL)
      delete defuse;
    if (liv !=NULL)
      delete liv;
}

//Compute dependence graph for a loop, using ArrayInterface and ArrayAnnoation
// TODO generate dep graph for the entire function and reuse it for all loops
LoopTreeDepGraph*  ComputeDependenceGraph(SgNode* loop, ArrayInterface* array_interface, ArrayAnnotation* annot)
{
ROSE_ASSERT(loop && array_interface&& annot);
//TODO check if its a canonical loop
// Prepare AstInterface: implementation and head pointer
AstInterfaceImpl faImpl_2 = AstInterfaceImpl(loop);
//AstInterface fa(&faImpl); // Using CPP interface to handle templates etc.
CPPAstInterface fa(&faImpl_2);
AstNodePtr head = AstNodePtrImpl(loop);
//AstNodePtr head = AstNodePtrImpl(body);
fa.SetRoot(head);

LoopTransformInterface::set_astInterface(fa);
LoopTransformInterface::set_arrayInfo(array_interface);
LoopTransformInterface::set_aliasInfo(array_interface);
LoopTransformInterface::set_sideEffectInfo(annot);
LoopTreeDepCompCreate* comp = new LoopTreeDepCompCreate(head,true,true);
// the third parameter sets supportNonFortranLoop to true
 // TODO when to release this?
// Retrieve dependence graph here!
if (false)
{
SgStatement* stmt = isSgStatement(loop);
ROSE_ASSERT (stmt != NULL);
std::cout<<"--------------------------------------------------------"<<std::endl;
std::cout<<"Debug: ComputeDependenceGraph() dumps the dependence graph for the loop at line :"<< stmt->get_file_info()->get_line()<<std::endl;
comp->DumpDep();
//comp->DumpTree();
std::cout<<"--------------------------------------------------------"<<std::endl;
}

// The following code was used when an entire function body with several loops
// is analyzed for dependence analysis. I keep it to double check the computation.

// Get the loop hierarchy :grab just a top one for now
// TODO consider complex loop nests like loop {loop, loop} and loop{loop {loop}}
LoopTreeNode * loop_root = comp->GetLoopTreeRoot();
ROSE_ASSERT(loop_root!=NULL);
//loop_root->Dump();
LoopTreeTraverseSelectLoop loop_nodes(loop_root, LoopTreeTraverse::PreOrder);
LoopTreeNode * cur_loop = loop_nodes.Current();
// three-level loop: i,j,k
AstNodePtr ast_ptr;
if (cur_loop)
{
//cur_loop->Dump();
//loop_nodes.Advance();
//loop_nodes.Current()->Dump();
//loop_nodes.Advance();
//loop_nodes.Current()->Dump();
ast_ptr = dynamic_cast<LoopTreeLoopNode*>(cur_loop)->GetOrigLoop();
// cout<<AstToString(ast_ptr)<<endl;
ROSE_ASSERT(ast_ptr!=NULL);
SgNode* sg_node = AstNodePtr2Sage(ast_ptr);
ROSE_ASSERT(sg_node == loop);
// cout<<"-------------Dump the loops in question------------"<<endl;
//   cout<<sg_node->class_name()<<endl;
return comp->GetDepGraph();
}
else
{
std::cout<<"Skipping a loop not recognized by LoopTreeTraverseSelectLoop ..."<<std::endl;
return NULL;
// Not all loop can be collected by LoopTreeTraverseSelectLoop right now
// e.g: loops in template function bodies
//ROSE_ASSERT(false);
}
}// End Of ComputeDependency Graph

// Return the loop invariant of a canonical loop
// Return NULL if the loop is not canonical
SgInitializedName* getLoopInvariant(SgNode* loop)
{
SgInitializedName* invarname = NULL;
if (!SageInterface::isCanonicalForLoop(loop, &invarname) )
return NULL;
return invarname;
}// End Of getLoopVariant


#if 1
 // Get the live-in and live-out variable sets for a for loop, 
  // recomputing liveness analysis if requested (useful after program transformation)
  // Only consider scalars for now, ignore non-scalar variables
  // Also ignore loop invariant variables.
  void GetLiveVariables(SgNode* loop, std::vector<SgInitializedName*> &liveIns,
      std::vector<SgInitializedName*> &liveOuts,bool reCompute/*=false*/)
  {
    // TODO reCompute : call another liveness analysis function on a target function
    if (reCompute)
      initialize_analysis(NULL,false);

    std::vector<SgInitializedName*> liveIns0, liveOuts0; // store the original one
    SgInitializedName* invarname = getLoopInvariant(loop);
    // Grab the filtered CFG node for SgForStatement
    SgForStatement *forstmt = isSgForStatement(loop);
    ROSE_ASSERT(forstmt);
    // Jeremiah's hidden constructor to grab the right one
    // Several CFG nodes are used for the same SgForStatement
    CFGNode cfgnode(forstmt,2);
    FilteredCFGNode<IsDFAFilter> filternode= FilteredCFGNode<IsDFAFilter> (cfgnode);
    // This one does not return the one we want even its getNode returns the
    // right for statement
    //FilteredCFGNode<IsDFAFilter> filternode= FilteredCFGNode<IsDFAFilter> (forstmt->cfgForBeginning());
    ROSE_ASSERT(filternode.getNode()==forstmt);

    // Check out edges
    vector<FilteredCFGEdge < IsDFAFilter > > out_edges = filternode.outEdges();
    //cout<<"Found edge count:"<<out_edges.size()<<endl;
    //SgForStatement should have two outgoing edges, one true(going into the loop body) and one false (going out the loop)
    ROSE_ASSERT(out_edges.size()==2);
    vector<FilteredCFGEdge < IsDFAFilter > >::iterator iter= out_edges.begin();
    //  std::vector<SgInitializedName*> remove1, remove2;
    for (; iter!=out_edges.end();iter++)
    {
      FilteredCFGEdge < IsDFAFilter > edge= *iter;
      // Used to verify CFG nodes in var.dot dump
      //x. Live-in (loop) = live-in (first-stmt-in-loop)
      if (edge.condition()==eckTrue)
      {
        SgNode* firstnode= edge.target().getNode();
        liveOuts0 = liv->getIn(firstnode);
        if (enable_debug)
          cout<<"Live-in variables for loop:"<<firstnode->get_file_info()->get_line()<<endl;
        for (std::vector<SgInitializedName*>::iterator iter = liveIns0.begin();
            iter!=liveIns0.end(); iter++)
        {
          SgInitializedName* name = *iter;
          if ((SageInterface::isScalarType(name->get_type()))&&(name!=invarname))
          {
            liveIns.push_back(*iter);
            //          remove1.push_back(*iter);
            if (enable_debug)
              cout<< name->get_qualified_name().getString()<<endl;
          }
        }
      }
      //x. live-out(loop) = live-in (first-stmt-after-loop)
      else if (edge.condition()==eckFalse)
      {
        SgNode* firstnode= edge.target().getNode();
        liveOuts0 = liv->getIn(firstnode);
        if (enable_debug)
          cout<<"Live-out variables for loop before line:"<<firstnode->get_file_info()->get_line()<< endl;
        for (std::vector<SgInitializedName*>::iterator iter = liveOuts0.begin();
            iter!=liveOuts0.end(); iter++)
        {
          SgInitializedName* name = *iter;
          if ((SageInterface::isScalarType(name->get_type()))&&(name!=invarname))
          {
            if (enable_debug)
              cout<< name->get_qualified_name().getString()<<endl;
            liveOuts.push_back(*iter);
            //          remove2.push_back(*iter);
          }
        }
      }
      else
      {
        cerr<<"Unexpected CFG out edge type for SgForStmt!"<<endl;
        ROSE_ASSERT(false);
      }
    } // end for (edges)
#if 0 // remove is not stable for unkown reasons
    // sort them for better search/remove 
    sort(liveIns.begin(),liveIns.end());
    sort(liveOuts.begin(),liveOuts.end());

    // Remove non-scalar variables 
    std::vector<SgInitializedName*>::iterator iter2;
    for (iter2=remove1.begin();iter2!=remove1.end();iter2++)
      remove(liveIns.begin(),liveIns.end(),*iter2);

    std::vector<SgInitializedName*>::iterator iter3;
    for (iter3=remove2.begin();iter3!=remove2.end();iter3++)
      remove(liveOuts.begin(),liveOuts.end(),*iter3);

    // Remove loop invariant variables
    remove(liveIns.begin(),liveIns.end(),invarname);
    remove(liveOuts.begin(),liveOuts.end(),invarname);
#endif
    // debug the final results
    if(enable_debug)
    {
      cout<<"Final Live-in variables for loop:"<<endl;
      for (std::vector<SgInitializedName*>::iterator iter = liveIns.begin();
          iter!=liveIns.end(); iter++)
      {
        SgInitializedName* name = *iter;
        cout<< name->get_qualified_name().getString()<<endl;
      }
      cout<<"Final Live-out variables for loop:"<<endl;
      for (std::vector<SgInitializedName*>::iterator iter = liveOuts.begin();
          iter!=liveOuts.end(); iter++)
      {
        SgInitializedName* name = *iter;
        cout<< name->get_qualified_name().getString()<<endl;
      }
    }

  } // end GetLiveVariables()

#endif

 static bool isStaticArrayRef (SgNode* ref)
  {
    bool ret = false;
    ROSE_ASSERT (ref !=NULL);
    if (SgPntrArrRefExp* aref = isSgPntrArrRefExp(ref))
    {
     // for multidimensional array references, getting the nested child SgPntrArrRef
     if (SgPntrArrRefExp* nestRef = isSgPntrArrRefExp(aref->get_lhs_operand_i()))
     return isStaticArrayRef (nestRef);
     SgVarRefExp* lhs = isSgVarRefExp (aref->get_lhs_operand_i());
     if (lhs != NULL)
       {
        SgVariableSymbol * varSym = isSgVariableSymbol (lhs->get_symbol());
        if (varSym!=NULL)
        {
        SgInitializedName * iname = varSym->get_declaration();
        if (isSgArrayType (iname->get_type()))
          ret = true;
        }
       }
     } 
    return ret;
  }


void CollectVisibleVariables(SgNode* loop, std::vector<SgInitializedName*>&resultVars,                                                               std::vector<SgInitializedName*>& invariantVars, 
                             bool scalarOnly/*=false*/)
  {
    ROSE_ASSERT(loop !=NULL);
    //Get the scope of the loop
#if 0 // Liao, 6/27/2014. This is wrong. we can have an inner loop enclosed within an outer loop
      // The inner loop's current scope is not the function body!
    SgScopeStatement* currentscope = isSgFunctionDeclaration(\
        SageInterface::getEnclosingFunctionDeclaration(loop))\
                                     ->get_definition()->get_body();
#endif
    SgScopeStatement* currentscope = SageInterface::getEnclosingNode<SgScopeStatement> (loop, false);
    ROSE_ASSERT(currentscope != NULL);

    SgInitializedName* invarname = getLoopInvariant(loop);
    Rose_STL_Container<SgNode*> reflist = NodeQuery::querySubTree(loop, V_SgVarRefExp);
    for (Rose_STL_Container<SgNode*>::iterator i=reflist.begin();i!=reflist.end();i++)
    {
      SgInitializedName* initname= isSgVarRefExp(*i)->get_symbol()->get_declaration();
      SgScopeStatement* varscope=initname->get_scope();
      // only collect variables which are visible at the loop's scope
      // varscope is equal or higher than currentscope 
      if ((currentscope==varscope)||(SageInterface::isAncestor(varscope,currentscope)))
      {
        // Skip non-scalar if scalarOnly is requested
        if ((scalarOnly)&& !SageInterface::isScalarType(initname->get_type()))
          continue;
        if (invarname!=initname)
            resultVars.push_back(initname);
      }
    } // end for()

    // collect loop invariants here
    Rose_STL_Container<SgNode*> loopnests= NodeQuery::querySubTree(loop, V_SgForStatement);
    for (Rose_STL_Container<SgNode*>::iterator iter=loopnests.begin();
        iter!=loopnests.end(); iter++)
    {
      SgForStatement* forstmt= isSgForStatement(*iter);
      SgInitializedName* invariant = getLoopInvariant(forstmt);
      if (invariant)
      {
        SgScopeStatement* varscope=invariant->get_scope();
        // only collect variables which are visible at the loop's scope
        // varscope is equal or higher than currentscope 
        if ((currentscope==varscope)||(SageInterface::isAncestor(varscope,currentscope)))
          invariantVars.push_back(invariant);
      }
    }
#if 0  // remove is not stable ??
    //skip loop invariant variable:
    SgInitializedName* invarname = getLoopInvariant(loop);
    remove(resultVars.begin(),resultVars.end(),invarname);
#endif
    //Remove duplicated items 
    sort(resultVars.begin(),resultVars.end());
    std::vector<SgInitializedName*>::iterator new_end= unique(resultVars.begin(),resultVars.end());
    resultVars.erase(new_end, resultVars.end());

    sort(invariantVars.begin(),invariantVars.end());
    new_end= unique(invariantVars.begin(),invariantVars.end());
    invariantVars.erase(new_end, invariantVars.end());
} // End Of CollectVisibleVariables                                                                                                                                                                                                                          
  //! Collect a loop's variables which cause any kind of dependencies. Consider scalars only if requested.  
  // depgraph may contain dependencies for the entire function enclosing the loop. So we need to ignore irrelevant ones with respect to the loop
  void CollectVariablesWithDependence(SgNode* loop, LoopTreeDepGraph* depgraph,std::vector<SgInitializedName*>& resultVars,bool scalarOnly/*=false*/)
  {
    ROSE_ASSERT(isSgForStatement(loop)&& depgraph);
    LoopTreeDepGraph::NodeIterator nodes = depgraph->GetNodeIterator();
    // For each node
    for (; !nodes.ReachEnd(); ++ nodes)
    {
      LoopTreeDepGraph::Node* curnode = *nodes;
      LoopTreeDepGraph::EdgeIterator edges = depgraph->GetNodeEdgeIterator(curnode, GraphAccess::EdgeOut);
      // If the node has edges
      if (!edges.ReachEnd())
      {
        // for each edge
        for (; !edges.ReachEnd(); ++edges)
        {
          LoopTreeDepGraph::Edge *e= *edges;
          //cout<<"dependence edge: "<<e->toString()<<endl;
          DepInfo info =e->GetInfo();
          // Indicate if the variable references happen within the loop
          bool insideLoop1=false, insideLoop2=false;

          SgScopeStatement * loopscope= SageInterface::getScope(loop);
          SgScopeStatement* varscope =NULL;
          SgNode* src_node = AstNodePtr2Sage(info.SrcRef());
          SgInitializedName* src_name=NULL;
          if (src_node)
          { //TODO May need to consider a wider concept of variable reference 
            //like AstInterface::IsVarRef()
            SgVarRefExp* var_ref = isSgVarRefExp(src_node);
            if (var_ref)
           {
              varscope= var_ref->get_symbol()->get_scope();
              src_name = var_ref->get_symbol()->get_declaration();
              // Ignore the local variables declared inside the loop
              if (SageInterface::isAncestor(loopscope,varscope))
                continue;
              if (SageInterface::isAncestor(loopscope,var_ref))
                insideLoop1= true;
            } //end if(var_ref)
          } // end if (src_node)
          SgNode* snk_node = AstNodePtr2Sage(info.SnkRef());
          SgInitializedName* snk_name=NULL;
          if (snk_node)
          {
            SgVarRefExp* var_ref = isSgVarRefExp(snk_node);
            if (var_ref)
            {
              varscope= var_ref->get_symbol()->get_scope();
              snk_name = var_ref->get_symbol()->get_declaration();
              if (SageInterface::isAncestor(loopscope,varscope))
                continue;
              if (SageInterface::isAncestor(loopscope,var_ref))
                insideLoop2= true;
            } //end if(var_ref)
          } // end if (snk_node)
          // Only collect the dependence relation involving 
          // two variables referenced within the loop
          if (insideLoop1&& insideLoop2)
          {
            if (scalarOnly)
            { // Only meaningful if both are scalars 
              if(SageInterface::isScalarType(src_name->get_type())
                  &&SageInterface::isScalarType(snk_name->get_type()))
              {
                resultVars.push_back(src_name);
                resultVars.push_back(snk_name);
              }
            }
            else
            {
              resultVars.push_back(src_name);
              resultVars.push_back(snk_name);
            }
          }
        } //end iterator edges for a node
      } // end if has edge
    } // end of iterate dependence graph 
    // remove duplicated items
    sort(resultVars.begin(), resultVars.end());
    std::vector<SgInitializedName*>::iterator new_end=unique(resultVars.begin(),resultVars.end());
    resultVars.erase(new_end,resultVars.end());
  }  // End Of CollectVariablesWithDependence

void AutoScoping(SgNode *sg_node, OmpSupport::OmpAttribute* attribute,LoopTreeDepGraph* depgraph)
{
  ROSE_ASSERT(sg_node&&attribute&&depgraph);
  ROSE_ASSERT (isSgForStatement(sg_node));
  // Variable liveness analysis: original ones and 
  // the one containing only variables with some kind of dependencies
     std::vector<SgInitializedName*> liveIns0, liveIns;
     std::vector<SgInitializedName*> liveOuts0, liveOuts;
  // Turn on recomputing since transformations have been done
  // GetLiveVariables(sg_node,liveIns,liveOuts,true);
  // TODO Loop normalization messes up AST
  // the existing analysis can not be called multiple times
  GetLiveVariables(sg_node,liveIns0,liveOuts0, false);
  // Remove loop invariant variable, which is always private 
  SgInitializedName* invarname = getLoopInvariant(sg_node);
  SgForStatement* for_stmt = isSgForStatement(sg_node);
  ROSE_ASSERT (for_stmt !=NULL);
  remove(liveIns0.begin(),liveIns0.end(),invarname);
  remove(liveOuts0.begin(),liveOuts0.end(),invarname);
  std::vector<SgInitializedName*> allVars,depVars, invariantVars, privateVars,lastprivateVars,
  firstprivateVars,reductionVars; // reductionResults;
  // Only consider scalars for now
  CollectVisibleVariables(sg_node,allVars,invariantVars,true);
  sort(allVars.begin(), allVars.end());
  CollectVariablesWithDependence(sg_node,depgraph,depVars,true);
  if (enable_debug)
  {
   cout<<"Debug after CollectVisibleVaribles ():"<<endl;
   for (std::vector<SgInitializedName*>::iterator iter = allVars.begin(); iter!= allVars.end();iter++)
   {
      cout<<(*iter)<<" "<<(*iter)->get_qualified_name().getString()<<endl;
   }
      cout<<"Debug after CollectVariablesWithDependence():"<<endl;
   for (std::vector<SgInitializedName*>::iterator iter = depVars.begin(); iter!= depVars.end();iter++)
   {
      cout<<(*iter)<<" "<<(*iter)->get_qualified_name().getString()<<endl;
   }
  }
    sort(liveIns0.begin(), liveIns0.end());
    sort(liveOuts0.begin(), liveOuts0.end());
    
 set_intersection(liveIns0.begin(),liveIns0.end(), depVars.begin(), depVars.end(),
 inserter(liveIns, liveIns.begin()));
 set_intersection(liveOuts0.begin(),liveOuts0.end(), depVars.begin(), depVars.end(),
 inserter(liveOuts, liveOuts.begin()));
 sort(liveIns.begin(), liveIns.end());
 sort(liveOuts.begin(), liveOuts.end());
 // shared: scalars for now: allVars - depVars, 
 //private:
 //---------------------------------------------
 //depVars- liveIns - liveOuts
 std::vector<SgInitializedName*> temp;
 set_difference(depVars.begin(),depVars.end(), liveIns.begin(), liveIns.end(),
 inserter(temp, temp.begin()));
 set_difference(temp.begin(),temp.end(), liveOuts.begin(), liveOuts.end(),
 inserter(privateVars, privateVars.end()));
 // loop invariants are private
 // insert all loops, including nested ones' visible invariants
 for(std::vector<SgInitializedName*>::iterator iter =invariantVars.begin();iter!=invariantVars.end(); iter++)
      privateVars.push_back(*iter);
      if(enable_debug)
      cout<<"Debug dump private:"<<endl;
      bool hasNormalization = SageInterface::trans_records.forLoopInitNormalizationTable[for_stmt];
      SgVariableSymbol* ndecl_sym = NULL;
      if( hasNormalization)
     {
     SgVariableDeclaration* ndecl = SageInterface::trans_records.forLoopInitNormalizationRecord[for_stmt].second;
     ndecl_sym = getFirstVarSym (ndecl);
     }
     for (std::vector<SgInitializedName*>::iterator iter = privateVars.begin(); iter!= privateVars.end();iter++)
     {
      string var_name = (*iter)->get_name().getString();
      bool skipAdd = false;
      if (hasNormalization && ndecl_sym == (*iter)->search_for_symbol_from_symbol_table ())
      {
      skipAdd = true;
      }
  if (!skipAdd)
    {
     attribute->addVariable(OmpSupport::e_private , var_name , *iter);
     if(enable_debug)
     cout<<(*iter)<<" "<<(*iter)->get_qualified_name().getString()<<endl;
     }
     }
 set_difference(liveOuts.begin(), liveOuts.end(), liveIns0.begin(), liveIns0.end(),
 inserter(lastprivateVars, lastprivateVars.begin()));
 if(enable_debug)
 cout<<"Debug dump lastprivate:"<<endl;
 for (std::vector<SgInitializedName*>::iterator iter = lastprivateVars.begin(); iter!= lastprivateVars.end();iter++)
 {
  attribute->addVariable(OmpSupport::e_lastprivate ,(*iter)->get_name().getString(), *iter);
  if(enable_debug)
  cout<<(*iter)<<" "<<(*iter)->get_qualified_name().getString()<<endl;
 }

    std::set< std::pair <SgInitializedName*, OmpSupport::omp_construct_enum > > reductionResults;
    SageInterface::ReductionRecognition ( isSgForStatement (sg_node), reductionResults);
    if(enable_debug)
    cout<<"Debug dump reduction:"<<endl;
    for (std::set< std::pair <SgInitializedName*, OmpSupport::omp_construct_enum > > ::iterator
    iter = reductionResults.begin(); iter!= reductionResults.end();iter++)
    {
    SgInitializedName* iname = (*iter).first;
    OmpSupport::omp_construct_enum optype = (*iter).second;
    attribute->addVariable (optype,iname->get_name().getString(), iname);
    if(enable_debug)
    cout<< iname->get_qualified_name().getString()<<endl;
    }
  if(enable_debug)
    cout<<"Debug dump firstprivate:"<<endl;
 
    std::vector<SgInitializedName*> temp2, temp3;
    set_difference(liveIns0.begin(), liveIns0.end(), liveOuts0.begin(),liveOuts0.end(),
    inserter(temp2, temp2.begin()));
    set_difference(temp2.begin(), temp2.end(), depVars.begin(), depVars.end(),
    //inserter(firstprivateVars, firstprivateVars.begin()));
    inserter(temp3, temp3.begin()));
    // Liao 6/27/2014
    // LiveIn only means may be used, not must be used, in the future. 
    // some liveIn variables may not show up at all in the loop body we concern about
    // So we have to intersect with visible variables to make sure we only put used variables into the firstprivate clause
    set_intersection (temp3.begin(), temp3.end(), allVars.begin(), allVars.end(), inserter (firstprivateVars, firstprivateVars.begin()));
    for (std::vector<SgInitializedName*>::iterator iter = firstprivateVars.begin(); iter!= firstprivateVars.end();iter++)
     {
     attribute->addVariable(OmpSupport::e_firstprivate ,(*iter)->get_name().getString(), *iter);
     if(enable_debug)
     cout<<(*iter)<<" "<<(*iter)->get_qualified_name().getString()<<endl;
     }
   } // end AutoScoping()

#if 0
  void DependenceElimination(SgNode* sg_node, LoopTreeDepGraph* depgraph, std::vector<DepInfo>& remainings,
                             OmpSupport::OmpAttribute* att,std::map<SgNode*, bool> &  indirect_table,
                             ArrayInterface* array_interface/*=0*/, ArrayAnnotation* annot/*=0*/)
   {
   //LoopTreeDepGraph * depgraph =  comp.GetDepGraph(); 
     LoopTreeDepGraph::NodeIterator nodes = depgraph->GetNodeIterator();
     if (enable_debug)
     {
      cout<<"Entering DependenceElimination ()"<<endl;
      cout<<"----------------------------------"<<endl;
      }
      // For each node
     for (; !nodes.ReachEnd(); ++ nodes)
     {
       LoopTreeDepGraph::Node* curnode = *nodes;
       LoopTreeDepGraph::EdgeIterator edges = depgraph->GetNodeEdgeIterator(curnode, GraphAccess::EdgeOut);
       // If the node has edges
       if (!edges.ReachEnd())
       {
       // for each edge
       for (; !edges.ReachEnd(); ++edges)
       {
        LoopTreeDepGraph::Edge *e= *edges;
        DepInfo info =e->GetInfo();
        if (enable_debug)
        cout<<"-------------->>> Considering a new dependence edge's info:\n"<<info.toString()<<endl;
        SgScopeStatement * currentscope= SageInterface::getScope(sg_node);
        SgScopeStatement* varscope =NULL;
        SgNode* src_node = AstNodePtr2Sage(info.SrcRef());
        SgInitializedName* src_name=NULL;
        // two variables will be set if source or snk nodes are variable references nodes
        SgVarRefExp* src_var_ref = NULL;
        SgVarRefExp* snk_var_ref = NULL;

  if (src_node)
    {
      SgVarRefExp* var_ref = isSgVarRefExp(src_node);
      if (var_ref)
      {
       src_var_ref = var_ref;
       varscope= var_ref->get_symbol()->get_scope();
       src_name = var_ref->get_symbol()->get_declaration();
       if (SageInterface::isAncestor(currentscope,varscope))
       {
       if (enable_debug)
       {
        cout<<"Eliminating a dep relation due to locally declared src variable"<<endl;
        info.Dump();
       }
       continue;
       }
       } //end if(var_ref)
     } // end if (src_node)
       SgNode* snk_node = AstNodePtr2Sage(info.SnkRef());
       SgInitializedName* snk_name=NULL;
   #if 1
             // x. Eliminate dependence relationship if one of the pair is thread local
             // -----------------------------------------------
             // either of the source or sink variables are thread-local: 
             // (within the scope of the loop's scope)
             // There is no loop carried dependence in this case 
             if (snk_node)
             {
              SgVarRefExp* var_ref = isSgVarRefExp(snk_node);
        snk_var_ref = var_ref;
	if (var_ref)
	 {
	 varscope= var_ref->get_symbol()->get_scope();
	 snk_name = var_ref->get_symbol()->get_declaration();
	 if (SageInterface::isAncestor(currentscope,varscope))
	 {
	 if (enable_debug)
	  {
	   cout<<"Eliminating a dep relation due to locally declared sink variable"<<endl;
	   info.Dump();
	  }
	   continue;
	  }
	  } //end if(var_ref)
	  } // end if (snk_node)
	 #endif
	  if (enable_debug)
	  cout<<"Neither source nor sink node is locally decalared variables."<<endl;
            //x. Eliminate a dependence if it is empty entry
	    // -----------------------------------------------
	    // Ignore possible empty depInfo entry
	      if (src_node==NULL||snk_node==NULL)
	       {
	         if (enable_debug)
	         {
	         cout<<"Eliminating a dep relation due to empty entry for either src or sink variables or both"<<endl;
	         info.Dump();
	         }
	         continue;
	         }

         if (enable_debug)
	 cout<<"Neither source nor sink node is empty entry."<<endl;
          bool isArray1=false, isArray2=false;
          AstInterfaceImpl faImpl=AstInterfaceImpl(sg_node);
          AstInterface fa(&faImpl);
          // If we have array annotation, use loop transformation interface's IsArrayAccess()
         if (array_interface&& annot)
         {
          LoopTransformInterface::set_astInterface(fa);
          LoopTransformInterface::set_arrayInfo(array_interface);
          LoopTransformInterface::set_sideEffectInfo(annot);
          isArray1= LoopTransformInterface::IsArrayAccess(info.SrcRef());
          isArray2= LoopTransformInterface::IsArrayAccess(info.SnkRef());
          }
          else // use AstInterface's IsArrayAccess() otherwise
          {
          isArray1= fa.IsArrayAccess(info.SrcRef());
          isArray2= fa.IsArrayAccess(info.SnkRef());
          }
 
          //if (isArray1 && isArray2) // changed from both to either to be aggressive, 5/25/2010
           if (isArray1 || isArray2)
           {
             if (enable_debug)
             cout<<"Either source or sink reference is an array reference..."<<endl;
 
             if ((info.GetDepType() & DEPTYPE_SCALAR)||(info.GetDepType() & DEPTYPE_BACKSCALAR))
             {
             if (enable_debug)
             cout<<"\t Dep type is scalar or backscalar "<<endl;
             if (src_var_ref || snk_var_ref) // at least one is a scalar: we have scalar vs. array
               {
              if (enable_debug)
              cout<<"Either source or sink reference is a scalar reference..."<<endl;

                 SgVarRefExp* one_var= src_var_ref?src_var_ref:snk_var_ref;
		  // non-pointer type or pointertype && no_aliasing, we skip it
/*		      if (!isPointerType(one_var->get_type()) ||AutoParallelization::no_aliasing )
		         {
		         if (enable_debug)
		          {
		         if (AutoParallelization::no_aliasing)
		     cout<<"Non-aliasing assumed, eliminating a dep relation due to scalar dep type for atleast one array variable (pointers used as arrays)"<<endl;
		         else
	cout<<"Found a non-pointer scalar, eliminating a dep relation due to the scalar dep type between a scalar and an array"<<endl;
		         info.Dump();
                   }
*/
                 continue;
                 }
               }
               else // both are arrays
              {
               if (enable_debug)
                   cout<<"\t both are arrray references "<<endl;
         /*      if (AutoParallelization::no_aliasing)
                 {
               if (enable_debug)
                 {
                 cout<<"Non-aliasing assumed, eliminating a dep relation due to scalar dep type for at least one array variable (pointers used      as arrays)"<<endl;
                     info.Dump();
                     }
                     continue;
                     }*/
	             // both are arrays and both are statically allocated ones
	             else if (isStaticArrayRef (src_node) && isStaticArrayRef (snk_node))
	             {
	             if (enable_debug)
	             {
	             cout<<"Eliminating a dep relation due to both references are references to static allocated arrays "<<endl;
	             info.Dump();
	             }
	             continue;
	             }
	             } // end both are arrays  
	             }
	             }

  if(att&& (src_name || snk_name)) // either src or snk might be an array reference 
  {
   std::vector<SgInitializedName*> scoped_vars;
   CollectScopedVariables(att, scoped_vars);
   std::vector<SgInitializedName*>::iterator hit1 = scoped_vars.end(), hit2 = scoped_vars.end();
   //for (hit1=scoped_vars.begin();hit1!=scoped_vars.end();hit1++)
   //  cout<<"scoped var:"<<*hit1 <<" name:"<<(*hit1)->get_name().getString()<<endl;
   if (src_name)
   hit1=find(scoped_vars.begin(),scoped_vars.end(),src_name);
   if (snk_name)
      hit2=find(scoped_vars.begin(),scoped_vars.end(),snk_name);
      if (hit1!=scoped_vars.end() || (hit2!=scoped_vars.end()))
      {
       if (enable_debug)
       {
       cout<<"Eliminating a dep relation due to at least one autoscoped variables"<<endl;
       info.Dump();
       }
       continue;
       }
       }

           if (b_unique_indirect_index )
           {
           if (indirect_table[src_node] && indirect_table[snk_node])
           {
           if (enable_debug)
           {
           cout<<"Eliminating a dep relation due to unique indirect indexed array references"<<endl;
           info.Dump();
           }
           continue;
           }
           }

          SgExpression* src_exp = isSgExpression(src_node);
          SgExpression* snk_exp = isSgExpression(snk_node);
          if (src_exp && snk_exp)
          {
          if (differentMemoryLocation (src_exp, snk_exp))
          {
          if (enable_debug)
          {
          cout<<"Eliminating a dep relation between two instances of the same data member from different parent aggregate data"<<endl;
          info.Dump();
          }
          continue;
          }
          }

    if (info.CommonLevel()==0)
    {
     if (enable_debug)
     {
       cout<<"Eliminating a dep relation due to lack of common enclosing loop nests: common level ==0"<<endl;
       info.Dump();
     }
       continue;
    }
  if (info.CarryLevel()!=0)
    {
    if (enable_debug)
     {
     cout<<"Eliminating a dep relation due to carryLevel != 0 (not carried by current loop level in question)"<<endl;
     info.Dump();
     }
     continue;
     }
     // Save the rest dependences which can not be ruled out 
     if (enable_debug)
     cout<<"\t this dep relation cannot be eliminated. saved into remaining depedence set."<<endl;
     remainings.push_back(info);
     } //end iterator edges for a node
     } // end if has edge
     } // end of iterate dependence graph 
     if (enable_debug)
     {
      cout<<"Exiting DependenceElimination ()"<<endl;
      cout<<"----------------------------------"<<endl;
     }
    }// end DependenceElimination()
#endif
    
void mapVarsToOmpAttribute(OmpSupport::OmpAttribute *omp_attribute,
                           enum omp_construct_enum mapVariant,
                           std::vector <SgInitializedName*> &varList)
{
//TODO:Check if there are duplicate variables in map clause

for(std::vector<SgInitializedName*>::iterator itr=varList.begin();itr!=varList.end();++itr)
 {
 SgInitializedName* i_name=isSgInitializedName(*itr);
 std::string str=i_name->get_name().getString();
 omp_attribute->addVariable(mapVariant,str,i_name);
 if(isSgArrayType(i_name->get_type()))
 {
 int dimCount=SageInterface::getDimensionCount(i_name->get_type());
 std::vector<SgExpression*> arrDimInfo=SageInterface::get_C_array_dimensions(i_name->get_type());
 std::vector < std::pair<SgExpression*,SgExpression*> > expr;
 switch(dimCount)
 {
 case 1:
         {
         std::pair<SgExpression*,SgExpression*> pair1(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(1)));
         expr.push_back(pair1);
         }
 break;
 case 2:
         {
         std::pair<SgExpression*,SgExpression*> pair11(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(1)));
         std::pair<SgExpression*,SgExpression*> pair12(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(2)));
         expr.push_back(pair11);
         expr.push_back(pair12);
         }
 break;
 case 3:
         {
	 std::pair<SgExpression*,SgExpression*> pair111(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(1)));
	 std::pair<SgExpression*,SgExpression*> pair112(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(2)));
	 std::pair<SgExpression*,SgExpression*> pair113(SageBuilder::buildIntVal(0),SageInterface::copyExpression(arrDimInfo.at(3)));
	 expr.push_back(pair111);
	 expr.push_back(pair112);
	 expr.push_back(pair113);
	 }
 break;
  }
	 (omp_attribute->array_dimensions).insert({i_name->get_symbol_from_symbol_table(),expr});
 }
 else if(isSgPointerType(i_name->get_type()))
 {
 //Array is Pointer type
 //Read Pragma above 
 //std::cout<<i_name->unparseToString()<<std::endl;
 SgStatement *declStmt=isSgStatement(i_name->get_declaration());
 //std::cout<<declStmt->unparseToString()<<std::endl;
 std::string arrName=i_name->get_name();
 //std::cout<<arrName<<std::endl; 
 int dimCount=storeDynArr[arrName].first;
 std::vector < std::pair<SgExpression*,SgExpression*> > expr;
 int x,y,z;
  switch(dimCount)
  {
   case 1:
   {
     x=(storeDynArr[arrName].second)[0];   
     std::pair<SgExpression*,SgExpression*> pair1(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(x));
     expr.push_back(pair1);
   }
  break;
   case 2:
   {
      x=(storeDynArr[arrName].second)[0];
      y=(storeDynArr[arrName].second)[1];
     std::pair<SgExpression*,SgExpression*> pair11(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(x));
     std::pair<SgExpression*,SgExpression*> pair12(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(y));
     expr.push_back(pair11);
     expr.push_back(pair12);
   }
  break;
   case 3:
   {
     x=(storeDynArr[arrName].second)[0];
     y=(storeDynArr[arrName].second)[1];
     z=(storeDynArr[arrName].second)[2];
     std::pair<SgExpression*,SgExpression*> pair111(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(x));
     std::pair<SgExpression*,SgExpression*> pair112(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(y));
     std::pair<SgExpression*,SgExpression*> pair113(SageBuilder::buildIntVal(0),SageBuilder::buildIntVal(z));
     expr.push_back(pair111);
     expr.push_back(pair112);
     expr.push_back(pair113);
   }
  break;
  }
   (omp_attribute->array_dimensions).insert({i_name->get_symbol_from_symbol_table(),expr});
}

} //end of for loop
}// end of mapVarsToOmpAttribute

#if 1
//TODO: find on which for loop reduction variable is present
void findReductionVars(SgForStatement *forStmt,std::set< std::pair<SgInitializedName*,OmpSupport::omp_construct_enum>> &reductionVars,OmpSupport::OmpAttribute *omp_attr)
{
ROSE_ASSERT(forStmt!=NULL);
Rose_STL_Container<SgNode*> forLoopList=NodeQuery::querySubTree(forStmt,V_SgForStatement);
int counter=forLoopList.size();
int c=0;
OmpSupport::OmpAttribute *ompAttrib=NULL;
SgForStatement *for_stmt=NULL;

for(Rose_STL_Container<SgNode*>::reverse_iterator iter=forLoopList.rbegin();iter!=forLoopList.rend();++iter)
{
std::set< std::pair<SgInitializedName*,OmpSupport::omp_construct_enum> > reductVars;
for_stmt=isSgForStatement(*iter);
{
SageInterface::ReductionRecognition(for_stmt,reductVars);
//std::set_difference(reductVars.begin(),reductVars.end(),actualreductVars.begin(),actualreductVars.end(),std::inserter(actualreductVars,actualreductVars.begin()));
if(reductVars.size()!=0)
{
if(forStmt==for_stmt)
omp_attr->addClause(OmpSupport::e_reduction);
else
{
ompAttrib=OmpSupport::buildOmpAttribute(OmpSupport::e_parallel_for,for_stmt,NULL);
ompAttrib->addClause(OmpSupport::e_reduction);
}
std::set<std::pair<SgInitializedName*,OmpSupport::omp_construct_enum>>::iterator it;
for(it=reductVars.begin();it!=reductVars.end();++it)
{
if(forStmt==for_stmt)
omp_attr->addVariable((*it).second,(*it).first->get_name(),(*it).first);
else
ompAttrib->addVariable((*it).second,(*it).first->get_name(),(*it).first);
}

/*
if(ompAttrib!=NULL && for_stmt!=forStmt)
{
OmpSupport::addOmpAttribute(ompAttrib,for_stmt);
OmpSupport::generatePragmaFromOmpAttribute(for_stmt);
}
*/
}
}
std::set_union(reductionVars.begin(),reductionVars.end(),reductVars.begin(),reductVars.end(),inserter(reductionVars,reductionVars.end()));
//reductionVars.insert(reductVars.begin(),reductVars.end());
}
}//end Of findReductionVars
#endif

#if 1
void recognizeCollapse(SgNode *node,OmpSupport::OmpAttribute *omp_attr){
ROSE_ASSERT(node && omp_attr);

Rose_STL_Container<SgNode*> loopList=NodeQuery::querySubTree(node,V_SgForStatement);
int counter=0;
for(Rose_STL_Container<SgNode*>::iterator iter=loopList.begin();iter!=loopList.end();++iter){
SgForStatement* for_stmt = isSgForStatement(*iter);
SgStatement *first_for_stmt=SageInterface::getFirstStatement(for_stmt);
SgStatement *last_for_stmt=SageInterface::getLastStatement(for_stmt);
//std::cout<<first_for_stmt->unparseToString()<<std::endl;
//std::cout<<last_for_stmt->unparseToString()<<std::endl;
if(first_for_stmt==last_for_stmt)
counter++;
else
{
counter++;
break;
}
}
if(counter>=1)
{
omp_attr->addClause(OmpSupport::e_collapse);
omp_attr->addExpression(OmpSupport::e_collapse,"", buildIntVal(counter));
}
}
#endif

void Offload(SgNode* node,LoopTreeDepGraph* depgraph,ArrayInterface *array_interface,ArrayAnnotation* annot)
{
SgNode *loop=node;
SgForStatement *forStmt=isSgForStatement(loop);
ROSE_ASSERT(forStmt!=NULL);
OmpSupport::OmpAttribute *omp_attribute = OmpSupport::buildOmpAttribute(e_target_data,forStmt,false);
OmpSupport::OmpAttribute *omp_sub_attrib = OmpSupport::buildOmpAttribute(e_parallel_for,NULL,false);

ROSE_ASSERT(omp_attribute != NULL);
ROSE_ASSERT(omp_sub_attrib!=NULL);

//omp_attribute->setOmpDirectiveType(OmpSupport::e_target);
//OmpSupport::addOmpAttribute(omp_attribute,loop);
//OmpSupport::generatePragmaFromOmpAttribute(loop);

/*
 * Collecting The Liveness Analysis and Dependence Analysis
*/
std::set<SgInitializedName*> liveIns0;
std::set<SgInitializedName*> liveOuts0;

SageInterface::getLiveVariables(liv,forStmt,liveIns0,liveOuts0);

std::vector<SgInitializedName*> liveIns(liveIns0.begin(),liveIns0.end());
std::vector<SgInitializedName*> liveOuts(liveOuts0.begin(),liveOuts0.end());
std::vector<SgInitializedName*> newLiveIns;
std::vector<SgInitializedName*> newLiveOuts;

SgInitializedName* invarname = getLoopInvariant(loop);
//std::cout<<invarname->unparseToString()<<std::endl;

#if 0
//Since container used for LiveIns0 and LiveOuts is set so we use erase instead of remove function
auto itr=liveIns0.find(invarname);
liveIns0.erase(itr);
itr=liveOuts0.find(invarname);
liveOuts0.erase(itr);
#endif

std::remove(liveIns.begin(),liveIns.end(),invarname);
std::remove(liveOuts.begin(),liveOuts.end(),invarname);

std::vector<SgInitializedName*> allVars,depVars,invariantVars,privateVars,lastprivateVars,firstprivateVars;

CollectVisibleVariables(loop,allVars,invariantVars,true);
std::sort(allVars.begin(),allVars.end());
CollectVariablesWithDependence(loop,depgraph,depVars,true);
std::sort(depVars.begin(),depVars.end());

//Reduction Variables Collection
std::set< std::pair<SgInitializedName*,OmpSupport::omp_construct_enum>> reductionVars;
findReductionVars(forStmt,reductionVars,omp_sub_attrib);
recognizeCollapse(forStmt,omp_sub_attrib);

std::set<SgInitializedName*> readOnlyVars,readVars,writeVars;
std::vector<SgNode*> readRefs,writeRefs;


Rose_STL_Container<SgNode*> loopList=NodeQuery::querySubTree(forStmt,V_SgForStatement);
Rose_STL_Container<SgNode*>::iterator f_iter=loopList.begin();
for(;f_iter!=loopList.end();++f_iter)
{
SageInterface::collectReadOnlyVariables(isSgForStatement(*f_iter),readOnlyVars,true);
SageInterface::collectReadWriteVariables(isSgForStatement(*f_iter),readVars,writeVars,true);
}
//SageInterface::collectReadOnlyVariables(forStmt,readOnlyVars,true);
//SageInterface::collectReadWriteVariables(forStmt,readVars,writeVars,true);


SageInterface::collectReadWriteRefs(forStmt,readRefs,writeRefs);

#if 1
//liveOuts-liveIns=tofrom
//liveins =to
//Print All Variables and Dependency Variables
//std::cout<<"For Loop At Line Number"<<forStmt->get_file_info()->get_line()<<"::";
std::cout<<forStmt->unparseToString()<<std::endl;
std::cout<<"Live In Vars"<<std::endl;
for(std::vector<SgInitializedName*>::const_iterator it=liveIns.begin();it!=liveIns.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Live Out Vars"<<std::endl;
for(std::vector<SgInitializedName*>::const_iterator it=liveOuts.begin();it!=liveOuts.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"All Vars"<<std::endl;
for(std::vector<SgInitializedName*>::const_iterator it=allVars.begin();it!=allVars.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Dependence Variables"<<std::endl;
for(std::vector<SgInitializedName*>::const_iterator it=depVars.begin();it!=depVars.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Read Only Variables"<<std::endl;
for(std::set<SgInitializedName*>::const_iterator it=readOnlyVars.begin();it!=readOnlyVars.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Read Variables"<<std::endl;
for(std::set<SgInitializedName*>::const_iterator it=readVars.begin();it!=readVars.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Write Variables"<<std::endl;
for(std::set<SgInitializedName*>::const_iterator it=writeVars.begin();it!=writeVars.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Reduction Variables"<<std::endl;
for(std::set<std::pair<SgInitializedName*,OmpSupport::omp_construct_enum>>::const_iterator it=reductionVars.begin();it!=reductionVars.end();++it){
std::cout<<((*it).first)->unparseToString()<<std::endl;
}
/*
std::cout<<"Read Reference Variables"<<std::endl;
for(std::vector<SgNode*>::const_iterator it=readRefs.begin();it!=readRefs.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
std::cout<<"Write Reference Variables"<<std::endl;
for(std::vector<SgNode*>::const_iterator it=writeRefs.begin();it!=writeRefs.end();++it){
std::cout<<(*it)->unparseToString()<<std::endl;
}
*/
#endif

//Conversion of Set Container to Vector Container
std::vector<SgInitializedName*> readVarsVec(readVars.begin(),readVars.end());
std::vector<SgInitializedName*> writeVarsVec(writeVars.begin(),writeVars.end());
std::vector <SgInitializedName*> reductVars;
for(std::set<std::pair<SgInitializedName*,OmpSupport::omp_construct_enum>>::iterator it=reductionVars.begin();it!=reductionVars.end();++it){
reductVars.push_back((*it).first);
}

//To Variables ReadVars-InvariantVars-ReductionVars
std::vector<SgInitializedName*> toVars,finalToVars;
std::set_difference(readVarsVec.begin(),readVarsVec.end(),invariantVars.begin(),invariantVars.end(),inserter(toVars, toVars.begin()));
std::set_difference(toVars.begin(),toVars.end(),reductVars.begin(),reductVars.end(),inserter(finalToVars,finalToVars.begin()));

//From Variables WriteVars-InvariantVars-ReductionVars
std::vector<SgInitializedName*> fromVars,finalFromVars;
std::set_difference(writeVarsVec.begin(),writeVarsVec.end(),invariantVars.begin(),invariantVars.end(),inserter(fromVars, fromVars.begin()));
std::set_difference(fromVars.begin(),fromVars.end(),reductVars.begin(),reductVars.end(),inserter(finalFromVars,finalFromVars.begin()));

//toFrom Variables 
std::vector<SgInitializedName*> toFromVars;
std::set_intersection(finalToVars.begin(),finalToVars.end(),finalFromVars.begin(),finalFromVars.end(),std::inserter(toFromVars,toFromVars.begin()));

toFromVars.insert(toFromVars.end(), reductVars.begin(), reductVars.end());
 
//std::cout<<"==================Size Of To From Vars===================="<<reductVars.size()<<std::endl;

//Modified To And From Variables after removing duplicates 
toVars.clear();fromVars.clear();
std::set_difference(finalToVars.begin(),finalToVars.end(),toFromVars.begin(),toFromVars.end(),std::inserter(toVars,toVars.begin()));
std::set_difference(finalFromVars.begin(),finalFromVars.end(),toFromVars.begin(),toFromVars.end(),std::inserter(fromVars,fromVars.begin()));

#if 1
//Add Clause
omp_attribute->addClause(OmpSupport::e_map);
//Add To Variables to attribute
if(toVars.size()!=0)
{
omp_attribute->setMapVariant(OmpSupport::e_map_to);
mapVarsToOmpAttribute(omp_attribute,OmpSupport::e_map_to,toVars);
}
if(fromVars.size()!=0)
{
//Add From Variables to attribute
omp_attribute->setMapVariant(OmpSupport::e_map_from);
mapVarsToOmpAttribute(omp_attribute,OmpSupport::e_map_from,fromVars);
}
if(toFromVars.size()!=0)
{
//Add ToFrom Variables to attribute
omp_attribute->setMapVariant(OmpSupport::e_map_tofrom);
mapVarsToOmpAttribute(omp_attribute,OmpSupport::e_map_tofrom,toFromVars);
}

#if 1
 //AutoScoping
 std::map<SgNode*, bool> indirect_array_table;
 #if 0
 if (b_unique_indirect_index) // uniform and collect indirect indexed array only when needed
  {
  // uniform array reference expressions
     uniformIndirectIndexedArrayRefs(isSgForStatement(loop));
     collectIndirectIndexedArrayReferences (loop, indirect_array_table);
  }
 #endif
OmpSupport::OmpAttribute* omp_par_att = buildOmpAttribute(e_unknown, NULL, false);
ROSE_ASSERT(omp_par_att != NULL);
//AutoScoping(loop, omp_par_att,depgraph);
 
omp_par_att->setOmpDirectiveType(OmpSupport::e_parallel_for);
//OmpSupport::addOmpAttribute(omp_par_att,loop);
//OmpSupport::generatePragmaFromOmpAttribute(loop);
#endif


//Attach Attribute to Statement
if(toVars.size()!=0 || fromVars.size()!=0 || toFromVars.size()!=0)
{
//if(isSgPragmaDeclaration((SageInterface::getPreviousStatement(forStmt,1)))==NULL)
//OmpSupport::addOmpAttribute(omp_sub_attrib,forStmt);
OmpSupport::addOmpAttribute(omp_attribute,forStmt);
//Generate Attribute
OmpSupport::generatePragmaFromOmpAttribute(forStmt);
OmpSupport::removeOmpAttribute(omp_attribute,forStmt);
delete omp_attribute;
}
//omp_attribute->print();
#endif


#if 1
/**********Experiment Code*************/
//This code make changes to the pragma
//statement added above outermost for loop

if(isSgPragmaDeclaration((SageInterface::getPreviousStatement((SageInterface::getPreviousStatement(forStmt,1)),1)))==NULL)
{
recognizeCollapse(forStmt,omp_sub_attrib);
OmpSupport::addOmpAttribute(omp_sub_attrib,forStmt);
OmpSupport::generatePragmaFromOmpAttribute(forStmt);
}

SgPragmaDeclaration *pragmaDecl=isSgPragmaDeclaration(SageInterface::getPreviousStatement(forStmt));
if(pragmaDecl!=NULL)
{
SgPragmaDeclaration *prevpragmaDecl=isSgPragmaDeclaration(SageInterface::getPreviousStatement(pragmaDecl));
//std::cout<<pragmaDecl->unparseToString()<<std::endl;
//std::cout<<forStmt->unparseToString()<<std::endl;
//ROSE_ASSERT(pragmaDecl!=NULL);
if(prevpragmaDecl!=NULL)
{
std::string pragmaString=pragmaDecl->unparseToString();
//std::cout<<pragmaString<<std::endl;
if(pragmaString!="")
{
char ch;
int i=0,pos=-1;
int countSpace=0;
while(i<pragmaString.length())
{
ch=pragmaString[i];
if(ch==' ')countSpace++;
if(countSpace==2)
{
pos=i;break;
}
i++;
}
const std::string strVal="target teams distribute";
const std::string part1str="omp";
//std::cout<<"Part1"<<part1str<<std::endl;
std::string part2str=pragmaString.substr(pos);
//std::cout<<"Part2"<<part2str<<std::endl;
std::string newpragstr=part1str+" "+strVal+part2str;
SgPragmaDeclaration *newpragDecl=SageBuilder::buildPragmaDeclaration(newpragstr,forStmt->get_scope());
//std::cout<<newpragDecl->unparseToString()<<std::endl;
SageInterface::replaceStatement(pragmaDecl,newpragDecl);
}//End of if(pragmaString!="")
}//End of  if(pragmaDecl!=NULL)
}//End of  if(prevpragmaDecl!=NULL)

/**************************************/
#endif

#if 0
//Dependence Elimination
vector<DepInfo>  remainingDependences;
//DependenceElimination(loop, depgraph, remainingDependences,omp_par_att, indirect_array_table, array_interface, annot);
 
 SgSourceFile* file = getEnclosingSourceFile(loop);
 std::string  filename = loop->get_file_info()->get_filename();
 int lineno= loop->get_file_info()->get_line();
 int colno= loop->get_file_info()->get_col();

  if (remainingDependences.size()>0)
  {
    // write log entries for failed attempts
    //isParallelizable = false;
    std::ostringstream oss;
    oss<<"Unparallelizable loop@" <<filename <<":" <<lineno<< ":" <<colno<<endl;
    //Rose::KeepGoing::File2StringMap[file]+= oss.str();

    #if 0
    //if (!enable_diff|| enable_debug) // diff user vs. autopar needs cleaner output
    if (enable_debug||enable_verbose) // diff user vs. autopar needs cleaner output
    {

     cout<<"====================================================="<<endl;
     cout<<"Unparallelizable loop at line:"<<sg_node->get_file_info()->get_line()<<" due to the following dependencies:"<<endl;
     for (vector<DepInfo>::iterator iter= remainingDependences.begin();iter != remainingDependences.end(); iter ++)
     {
      DepInfo di = *iter;
      cout<<di.toString()<<endl;
      if (enable_distance)
      {
      if (di.rows()>0 && di.cols()>0)
      {
      int dist = abs((di.Entry(0,0)).GetAlign());
      if (dist < dep_dist)
         dep_dist = dist;
          }
         }
         }
        if (enable_distance)
        cout<<"The minimum dependence distance of all dependences for the loop is:"<<dep_dist<<endl;
    }
  #endif
   }
     else
     {
     // write log entries for success
       std::ostringstream oss;
       oss<<"Auto parallelized a loop@" <<filename <<":" <<lineno<< ":" <<colno<<endl;
     //  Rose::KeepGoing::File2StringMap[file]+= oss.str();
 
       //if (!enable_diff || enable_debug)
      #if 0
      if (enable_debug || enable_verbose)
       {
        cout<<"====================================================="<<endl;
        cout<<"Automatically parallelized a loop at line:"<<sg_node->get_file_info()->get_line()<<endl;
       }
       #endif
     }

      // comp.DetachDepGraph();// TODO release resources here
     //X.  Attach OmpAttribute to the loop node if it is parallelizable 
   //  if (isParallelizable)
   //  {
     //= OmpSupport::buildOmpAttribute(OmpSupport::e_parallel_for,sg_node);
     omp_par_att->setOmpDirectiveType(OmpSupport::e_parallel_for);
      #if 0
      if (enable_debug)
      {
      cout<<"attaching auto generated OMP att to sg_node "<<sg_node->class_name();
      cout<<" at line "<<isSgLocatedNode(loop)->get_file_info()->get_line()<<endl;
      }
      #endif
      OmpSupport::addOmpAttribute(omp_par_att,loop);
 
      // Output patch text to the log also
    //  Rose::KeepGoing::File2StringMap[file]+= OmpSupport::generateDiffTextFromOmpAttribute (loop);
 
      // 6. Generate and insert #pragma omp parallel for 
      // Liao, 2/12/2010
      // In the enable_diff mode, we don't want to generate pragmas from compiler-generated OmpAttribute.
     // Comparing OmpAttributes from both sources is enough
     
     // if (! enable_diff)
       OmpSupport::generatePragmaFromOmpAttribute(loop);
   //   }
   //  else // Not parallelizable, release resources.
   //  {
      delete omp_par_att;
   //  } 
   #endif
}  //End Of Offload

bool parallelizeOutermostLoop(SgNode* loop,ArrayInterface *array_interface,ArrayAnnotation* annot){
bool isParallelizable=false;
ROSE_ASSERT(loop&& array_interface && annot);
ROSE_ASSERT(isSgForStatement(loop));
int dep_dist = 999999; // the minimum dependence distance of all dependence relations for a loop. 

SgNode* sg_node = loop;
LoopTreeDepGraph* depgraph= ComputeDependenceGraph(sg_node, array_interface, annot);
if (depgraph==NULL)
{
std::cout<<"Warning: skipping a loop at line "<< sg_node->get_file_info()->get_line()<< " since failed to compute depgraph for it:"; 
//<<sg_node->unparseToString()<<endl;
return false;
}
//SgBasicBlock *bblock=SageBuilder::buildBasicBlock(SageInterface::copyStatement(isSgStatement(loop)));
//SageInterface::replaceStatement(isSgStatement(loop), bblock);
//sg_node=isSgNode(SageInterface::getFirstStatement(bblock, false));
Offload(sg_node,depgraph ,array_interface,annot);

return isParallelizable;
}

 /**
  *   *Experiment Code to Find Dynamic Arrays
  *   * Declare pragma in global scope for dynamic arrays as #pragma dynamic_array(a[20],b[20][30])
  *   */
 void findDynamicArray(SgNode* node){
 Rose_STL_Container<SgNode*> findDynamicPragmas=NodeQuery::querySubTree(node,V_SgPragmaDeclaration);
 Rose_STL_Container<SgNode*>::iterator iter;
 for(iter=findDynamicPragmas.begin();iter!=findDynamicPragmas.end();++iter)
 {
 SgPragmaDeclaration *pragmaDecl=isSgPragmaDeclaration(*iter);
 ROSE_ASSERT(pragmaDecl);
 std::string pragmaString=(pragmaDecl->get_pragma())->get_name();
 std::string workString=pragmaString.substr(13);
 //std::cout<<"Work String"<<workString<<std::endl;
 int len=workString.length();
 int i=0;
 std::string arrName;
 std::string digitVal;
 int dimCounter=0;
 while(i<len)
 {
 char ch=workString[i];
 switch(ch)
 {
 case '[':
 dimCounter++;
 if(storeDynArr.empty())
 {
 std::vector<int> vec;
 std::pair< int , std::vector<int> > arrDim(dimCounter,vec);
 storeDynArr.insert({arrName,arrDim});
 //std::cout<<"\n\n\narrName==="<<arrName<<std::endl;
 }
 else
 storeDynArr[arrName].first=dimCounter;
 break;
 case ']':
 //std::cout<<digitVal<<std::endl;
 (storeDynArr[arrName].second).push_back(stoi(digitVal));
 //std::cout<<"============="<<(storeDynArr[arrName].first)<<std::endl;
 //std::cout<<"============="<<(storeDynArr[arrName].second)[0]<<std::endl;
 digitVal="";
 break;
 case ',':arrName="";dimCounter=0;
 break;
 default: 
 if((ch>='A'&&ch<='Z')||(ch>='a'&&ch<='z')||(ch=='_'))
 arrName+=ch;
 else if(ch>='0' && ch<='9')
 digitVal+=ch;
 }//end of switch
 ++i;
 }//end of while
 }
 
 #if 0
 std::cout<<"Size of Dynamic Array"<<storeDynArr.size()<<std::endl;
 
 std::map<std::string,std::pair<int,std::vector<int>>>::iterator i;
 for(i=storeDynArr.begin();i!=storeDynArr.end();++i)
 {
  std::cout<<"Array Name"<<i->first<<std::endl;
  //std::cout<<"Array Dim"<<(i->second).first<<std::endl;
 // std::cout<<"Array Dim Values"<<(i->second).second<<std::endl;
 }
 #endif

 }

void findForLoops(SgNode* node){
SgFunctionDefinition *funcDef=isSgFunctionDefinition(node);
ROSE_ASSERT(funcDef!=NULL);
SgBasicBlock *funcBody=funcDef->get_body();
ROSE_ASSERT(funcBody!=NULL);
Rose_STL_Container<SgNode*> forLoopList=NodeQuery::querySubTree(funcBody,V_SgForStatement);
Rose_STL_Container<SgNode*>::iterator i;
for(i=forLoopList.begin();i!=forLoopList.end();)
{
SgForStatement *forStmt=isSgForStatement(*i);
ROSE_ASSERT(forStmt!=NULL);
//std::cout<<forStmt->unparseToString()<<std::endl;

//SageInterface::normalizeForLoopInitDeclaration(forStmt);

Rose_STL_Container<SgNode*> nestForList=NodeQuery::querySubTree(forStmt,V_SgForStatement);
i+=nestForList.size();

AstInterfaceImpl ast_inter(funcBody);
CPPAstInterface  cpp_ast_inter(&ast_inter);
OperatorInlineRewrite()(cpp_ast_inter, AstNodePtrImpl(funcBody));

ArrayAnnotation* annot = ArrayAnnotation::get_inst();
ArrayInterface array_interface(*annot);
array_interface.initialize(cpp_ast_inter, AstNodePtrImpl(funcDef));
array_interface.observe(cpp_ast_inter);
LoopTransformInterface::set_aliasInfo(&array_interface);
parallelizeOutermostLoop(forStmt, &array_interface, annot);
}
}

void forLoopNormalization(SgNode *node){
SgFunctionDefinition *funcDef=isSgFunctionDefinition(node);
ROSE_ASSERT(funcDef!=NULL);
SgBasicBlock *funcBody=funcDef->get_body();
ROSE_ASSERT(funcBody!=NULL);
Rose_STL_Container<SgNode*> forLoopList=NodeQuery::querySubTree(funcBody,V_SgForStatement);
Rose_STL_Container<SgNode*>::iterator i;
for(i=forLoopList.begin();i!=forLoopList.end();++i)
SageInterface::normalizeForLoopInitDeclaration(isSgForStatement(*i));
}

void forLoopDenormalization(SgNode *node)
{
SgFunctionDefinition *funcDef=isSgFunctionDefinition(node);
ROSE_ASSERT(funcDef!=NULL);
SgBasicBlock *funcBody=funcDef->get_body();
ROSE_ASSERT(funcBody!=NULL);
Rose_STL_Container<SgNode*> forLoopList=NodeQuery::querySubTree(funcBody,V_SgForStatement);
Rose_STL_Container<SgNode*>::iterator i;
for(i=forLoopList.begin();i!=forLoopList.end();++i)
SageInterface::unnormalizeForLoopInitDeclaration(isSgForStatement(*i));
}


void findCandidateFuncDef(SgNode* node){
ROSE_ASSERT(node!=NULL);
Rose_STL_Container<SgNode*> funcDefList=NodeQuery::querySubTree(node,V_SgFunctionDefinition);
Rose_STL_Container<SgNode*>::iterator it;
for(it=funcDefList.begin();it!=funcDefList.end();++it)
{
 SgFunctionDefinition *funcDef=isSgFunctionDefinition(*it);
 ROSE_ASSERT(funcDef!=NULL);
 if(funcDef->get_file_info()->isSameFile(isSgFile(node)))
 {
 forLoopNormalization(funcDef);
 findForLoops(funcDef);
 forLoopDenormalization(funcDef);
// std::cout<<funcDef->unparseToString()<<std::endl;
 }
}
}

#if 0
void addBlockScopeToPragma(SgNode *node){
Rose_STL_Container<SgNode*> pragmaList=NodeQuery::querySubTree(node,V_SgOmpTargetDataStatement);
std::cout<<pragmaList.size()<<std::endl;
for(Rose_STL_Container<SgNode*>::iterator it=pragmaList.begin();it!=pragmaList.end();++it)
{
//SgOmpTargetDataStatement *omp_decl=isSgOmpTargetDataStatement(*it);
//ROSE_ASSERT(omp_decl!=NULL);
//std::cout<<omp_decl<<std::endl;
//std::cout<<(*it)->unparseToString()<<std::endl;
//std::cout<<(omp_decl->get_body())->unparseToString()<<std::endl;
}
}
#endif

int main(int argc,char *argv[])
{
AttachedPreprocessingInfoType buffer;
ROSE_INITIALIZE;
SgProject *project=frontend(argc,argv);
ROSE_ASSERT(project!=NULL);
//Initialize Analysis
initialize_analysis(project,false);
SgFilePtrList &fileList=project->get_fileList();
SgFilePtrList::iterator iter;
for(iter=fileList.begin();iter!=fileList.end();++iter)
{
SgFile *file=isSgFile(*iter);
ROSE_ASSERT(file!=NULL);
SgSourceFile *sfile=isSgSourceFile(file);
ROSE_ASSERT(sfile!=NULL);
SgGlobal *globScope=sfile->get_globalScope();
ROSE_ASSERT(globScope!=NULL);
#if 0
Rose_STL_Container<SgNode*> globalStmtList=NodeQuery::querySubTree(globScope,V_SgStatement,AstQueryNamespace::ChildrenOnly);
Rose_STL_Container<SgNode*>::iterator iter;
for(iter=globalStmtList.begin();iter!=globalStmtList.end();++iter)
{
SgStatement *stmt=isSgStatement(*iter);
ROSE_ASSERT(stmt!=NULL);
if(stmt->get_file_info()->isSameFile(isSgFile(sfile)))
{firstStmt=stmt;break;}
}
#endif
firstStmt=SageInterface::getFirstStatement(globScope,false);
SageInterface::cutPreprocessingInfo(firstStmt, PreprocessingInfo::before, buffer);
findDynamicArray(sfile);
findCandidateFuncDef(sfile);
SageInterface::pastePreprocessingInfo(firstStmt,PreprocessingInfo::before,buffer);
//std::cout<<firstStmt->unparseToString()<<std::endl;
//std::cout<<SageInterface::findMain(sfile)->unparseToCompleteString()<<std::endl;
//processOpenMP(sfile);
//std::cout<<sfile->unparseToCompleteString()<<std::endl;
//OmpSupport::processOpenMP(sfile);
//addBlockScopeToPragma(sfile);
}
release_analysis();

//generateAstGraph(project, 20000, "astGraph");
//generateDOT(*project);
AstTests::runAllTests(project);
//std::cout<<project->unparseToString()<<std::endl;

project->unparse();
}

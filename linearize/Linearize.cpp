/*
 * Linearize.cpp
 *
 *  Created on: Mar 8, 2019
 *      Author: cdac01
 */

//Rose Header
#include "rose.h"

//system headers
#include <iostream>
#include <cstring>
#include <vector>
#include <map>
#include <algorithm>

//Linearize Headers
#include "Linearize.h"
#include "ArrNameDimInfo.cpp"

using namespace std;
using namespace SageBuilder;
//using namespace SageInterface;


static SgScopeStatement *mainBodyScope;
static SgStatement *firstMainBodyStmt;

static AttachedPreprocessingInfoType saveBuff;
static SgLocatedNode *locatedNode;
static int flag=false;
//This Map stores the unique height ,width or slice names for a particular array upto three dimensions
std::map <std::string,std::string> uniqNames;

#if 0
class SimpleInstrumentation : public AstSimpleProcessing
{
public:
virtual void visit(SgNode *node);
};
#endif

void SimpleInstrumentation :: visit(SgNode *node)
{
if(!flag)
if(isSgVariableDeclaration(node)!=NULL||isSgFunctionDeclaration(node)!=NULL)
{
flag=true;
locatedNode=isSgLocatedNode(node);
}
}


SgVariableSymbol* getSymbolFromName(SgBasicBlock* block, string varStr)
{

  NodeQuerySynthesizedAttributeType vars = NodeQuery::querySubTree(block, V_SgScopeStatement);

  NodeQuerySynthesizedAttributeType::const_iterator it = vars.begin();


  for(it= vars.begin(); it != vars.end(); it++)
    {
      SgScopeStatement* outer_scope = isSgScopeStatement(*(it));

      SgVariableSymbol* sym = outer_scope->lookup_var_symbol(varStr);

      if(sym!= NULL)
        return sym;
    }

  return NULL;
}

//! Check if an expression is an array access. If so, return its name and subscripts if requested.
// Based on AstInterface::IsArrayAccess()

bool isArrayReference(SgExpression* ref,
                      SgExpression** arrayName/*=NULL*/,
                      vector<SgExpression*>* subscripts/*=NULL*/)
{
  SgExpression* arrayRef=NULL;

  if (ref->variantT() == V_SgPntrArrRefExp) {
    if (subscripts != 0 || arrayName != 0) {
      SgExpression* n = ref;
      while (true) {
        SgPntrArrRefExp *arr = isSgPntrArrRefExp(n);
        if (arr == 0)
          break;
        n = arr->get_lhs_operand();
        // store left hand for possible reference exp to array variable
        if (arrayName!= 0)
          arrayRef = n;
        // right hand stores subscripts
        if (subscripts != 0){
          subscripts->push_back(arr->get_rhs_operand());
          //cout << "sub: " << (arr->get_rhs_operand())->unparseToString() << endl;
        }
      } // end while
      if  (arrayName !=NULL)
        {
          *arrayName = arrayRef;
        }
    }
    return true;
  }
  return false;
}

int getDimension(const SgInitializedName* var, SgType* var_type)
{
  if(var_type == NULL)
    var_type = var->get_type();

  if(isSgArrayType (var_type))
    {
      return SageInterface::getDimensionCount(isSgArrayType(var_type)) ;
    }
  else if(isSgPointerType(var_type)) // float **
    {
      int dim=0;
      while(true)
        {
          dim++;
          var_type = isSgPointerType(var_type)->get_base_type();

          ROSE_ASSERT(var_type);

          if(!isSgPointerType(var_type))
            return dim; // reached base type, we can return
        }
    }
  else if(isSgTypedefType(var_type))
    {

      SgType* base_type = isSgTypedefType(var_type)->get_base_type();

      return getDimension(var, base_type);

    }
  return 0;
}


void Linearize::createMallocPtrStmt(string name,SgType *type,int dim,SgScopeStatement *scope,SgVariableDeclaration *targetDecl)
{
	SgExpression *mallocExpr=NULL;
	SgExpression *sizeofExpr=buildSizeOfOp(type);
	SgExprListExp *mallocArgList=buildExprListExp();
	if(dim==1)
	{
	string height="height_"+name;
	string heightName=(uniqNames.find(height))->second;
	SgExpression *height_expr=buildVarRefExp(SgName(heightName),scope);
	mallocArgList->append_expression(buildMultiplyOp(sizeofExpr,height_expr));
	}
	else if(dim==2)
	{
	string height="height_"+name;
	string width="width_"+name;
        string heightName=(uniqNames.find(height))->second;
        string widthName=(uniqNames.find(width))->second;
	SgExpression *height_expr=buildVarRefExp(SgName(heightName),scope);
	SgExpression *width_expr=buildVarRefExp(SgName(widthName),scope);
	mallocArgList->append_expression(buildMultiplyOp(sizeofExpr,buildMultiplyOp(height_expr,width_expr)));
	}
	else if(dim==3)
	{
	string height="height_"+name;
	string width="width_"+name;
	string slice="slice_"+name;
	string heightName=(uniqNames.find(height))->second;//uniqNames[height];
        string widthName=(uniqNames.find(width))->second;//uniqNames[width];
        string sliceName=(uniqNames.find(slice))->second;//uniqNames[slice];
	SgExpression *height_expr=buildVarRefExp(SgName(heightName),scope);
	SgExpression *width_expr=buildVarRefExp(SgName(widthName),scope);
	SgExpression *slice_expr=buildVarRefExp(SgName(sliceName),scope);
	mallocArgList->append_expression(buildMultiplyOp(sizeofExpr,buildMultiplyOp(height_expr, buildMultiplyOp(width_expr, slice_expr))));
	}
	if(isSgGlobal(scope)!=NULL)
	{
		SgVariableDeclaration *newArrPtrDecl=buildVariableDeclaration(SgName(name),buildPointerType(type),NULL,scope);
		SageInterface::insertStatementAfter(targetDecl, newArrPtrDecl);
	//	SgFunctionDeclaration *mainDecl=SageInterface::findMain(scope);
	//	SgScopeStatement *mainBodyScope=mainDecl->get_definition()->get_body()->get_scope();
		mallocExpr=buildCastExp(buildFunctionCallExp(SgName("malloc"),buildPointerType(type),mallocArgList,mainBodyScope),buildPointerType(type));
		SgExprStatement *exprStmt=buildAssignStatement(buildVarRefExp(SgName(name),mainBodyScope),mallocExpr);
       //	SgStatement *targetStmt=SageInterface::getFirstStatement(mainBodyScope);
       		SgStatement *targetStmt=firstMainBodyStmt;
		SageInterface::insertStatementBefore(targetStmt,exprStmt);
	}
	else
	{
		mallocExpr=buildCastExp(buildFunctionCallExp(SgName("malloc"),buildPointerType(type),mallocArgList,scope),buildPointerType(type));
		SgVariableDeclaration *newArrPtrDecl=buildVariableDeclaration(SgName(name),buildPointerType(type),buildAssignInitializer(mallocExpr),scope);
		SgStatement *targetStmt=isSgStatement(targetDecl);
		SageInterface::insertStatementAfter(targetStmt,newArrPtrDecl);
	}
}

/*
 * This Function is used to initialize the dimension of array in functions which contain kernel and hence array 
 *void function(int a[N],b[N],c[N])
 *
 */
#if 0
void initDimensionArrayInFunc(SgInitializedName *iname)
{
ROSE_ASSERT(iname!=NULL);
string name=iname->name;

SgVariableDeclaration *varDecl=buildVariableDeclaration(SgName(name),buildIntType(),);

}
#endif 

SgFunctionDeclaration* Linearize::getFirstFunctionDeclaration(SgNode *node)
{
	SgFunctionDeclaration *firstFuncDecl=NULL;
	Rose_STL_Container<SgNode*> funcDeclList=NodeQuery::querySubTree(node,V_SgFunctionDeclaration);
	for(Rose_STL_Container<SgNode*>::iterator iter=funcDeclList.begin();iter!=funcDeclList.end();iter++)
	{
		SgFunctionDeclaration *funcDecl=isSgFunctionDeclaration(*iter);
		ROSE_ASSERT(funcDecl!=NULL);
		if(funcDecl->get_file_info()->isCompilerGenerated()==false)
		{
			firstFuncDecl=funcDecl;
			break;
		}
	}
	return firstFuncDecl;
}


void Linearize::convertToPointerArray(SgNode *node)
{
SgStatement *targetStmt=firstMainBodyStmt;
SgFunctionDeclaration *firstFuncDecl=getFirstFunctionDeclaration(node);
Rose_STL_Container<SgNode*> varDecList=NodeQuery::querySubTree(node,V_SgVariableDeclaration);
vector<SgExpression*> storeDim;

for(Rose_STL_Container<SgNode*>::iterator it=varDecList.begin();it!=varDecList.end();it++)
{
	SgVariableDeclaration *varDecl=isSgVariableDeclaration(*it);
#if 0	
	if(!(varDecl->get_file_info()->isSameFile(isSgFile(node))))
	cout<<varDecl->get_file_info()->get_filename()<<endl;
#endif
	if((varDecl->get_file_info()->isSameFile(isSgFile(node)))||varDecl->get_file_info()->isTransformation())
	{
	SgInitializedName *iname=SageInterface::getFirstInitializedName(varDecl);
	SgScopeStatement *varDeclScope=iname->get_scope();
	string varname=iname->get_name();
	SgType *type=iname->get_type();
	if(isSgArrayType(type)!=NULL)
	{
		 storeDim=SageInterface::get_C_array_dimensions(type);
		 arrNameDimInfo.insert({varname,storeDim.size()-1});
		 arrNameDimValuesInfo.insert({varname,storeDim});
		if(storeDim.size()-1==1)
		{
		  SgExpression *heightExpr=SageInterface::copyExpression(storeDim.at(1));
                   string height="height_"+varname;
                   string heightUname=SageInterface::generateUniqueVariableName(varDeclScope,height);
                   uniqNames.insert({height,heightUname});
		  SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(heightExpr,buildIntType()),varDeclScope);
		  if(isSgGlobal(varDeclScope)!=NULL)
		  {
                     SageInterface::insertStatementBefore(targetStmt,heightDecl,true);
		  }
		  else
		  {
		   SageInterface::insertStatementBefore(varDecl, heightDecl,true);
		  } 
		 //SageInterface::setStatic(heightDecl);
		 // SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("height__"+varname,firstFuncDecl->get_scope()),heightExpr),true);
		  createMallocPtrStmt(varname,type->findBaseType(),storeDim.size()-1,varDeclScope,varDecl);
		  SageInterface::removeStatement(varDecl);
		}
		else if(storeDim.size()-1==2)
		{
		 SgExpression *heightExpr=SageInterface::copyExpression(storeDim.at(1));
		 SgExpression *widthExpr=SageInterface::copyExpression(storeDim.at(2));
                 string height="height_"+varname;
                 string heightUname=SageInterface::generateUniqueVariableName(varDeclScope,height);
                 uniqNames.insert({height,heightUname});
                 string width="width_"+varname;
                 string widthUname=SageInterface::generateUniqueVariableName(varDeclScope,width);
                 uniqNames.insert({width,widthUname});
		 SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(heightExpr,buildIntType()),varDeclScope);
		 SgVariableDeclaration *widthDecl=buildVariableDeclaration(SgName(widthUname),buildIntType(),buildAssignInitializer(widthExpr,buildIntType()),varDeclScope);
		  if(isSgGlobal(varDeclScope)!=NULL)
                  {
                     SageInterface::insertStatementBefore(targetStmt,heightDecl,true);
		     SageInterface::insertStatementBefore(targetStmt, widthDecl,true);
                  }
		  else
		  {
		     SageInterface::insertStatementBefore(varDecl, heightDecl,true);
		     SageInterface::insertStatementBefore(varDecl, widthDecl,true);
		  }
		 //SageInterface::setStatic(heightDecl);
		// SageInterface::setStatic(widthDecl);
		// SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("height__"+varname,firstFuncDecl->get_scope()),heightExpr),true);
		// SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("width__"+varname,firstFuncDecl->get_scope()),widthExpr),true);
		 createMallocPtrStmt(varname,type->findBaseType(),storeDim.size()-1,varDeclScope,varDecl);
		 SageInterface::removeStatement(varDecl);
		}
		else if(storeDim.size()-1==3)
		{
		 SgExpression *heightExpr=SageInterface::copyExpression(storeDim.at(1));
		 SgExpression *widthExpr=SageInterface::copyExpression(storeDim.at(2));
		 SgExpression *sliceExpr=SageInterface::copyExpression(storeDim.at(3));
		 string height="height_"+varname;
                 string heightUname=SageInterface::generateUniqueVariableName(varDeclScope,height);
                 uniqNames.insert({height,heightUname});
                 string width="width_"+varname;
                 string widthUname=SageInterface::generateUniqueVariableName(varDeclScope,width);
                 uniqNames.insert({width,widthUname});
		 string slice="slice_"+varname;
                 string sliceUname=SageInterface::generateUniqueVariableName(varDeclScope,slice);
                 uniqNames.insert({slice,sliceUname});

		 SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(heightExpr,buildIntType()),varDeclScope);
		 SgVariableDeclaration *widthDecl=buildVariableDeclaration(SgName(widthUname),buildIntType(),buildAssignInitializer(widthExpr,buildIntType()),varDeclScope);
		 SgVariableDeclaration *sliceDecl=buildVariableDeclaration(SgName(sliceUname),buildIntType(),buildAssignInitializer(sliceExpr,buildIntType()),varDeclScope);
	
		 if(isSgGlobal(varDeclScope)!=NULL)
                  {
                     SageInterface::insertStatementBefore(targetStmt,heightDecl,true);
                     SageInterface::insertStatementBefore(targetStmt,widthDecl,true);
		     SageInterface::insertStatementBefore(targetStmt,sliceDecl,true);
                  }
		 else
		  {
		     SageInterface::insertStatementBefore(varDecl, heightDecl,true);
		     SageInterface::insertStatementBefore(varDecl, widthDecl,true);
		     SageInterface::insertStatementBefore(varDecl, sliceDecl,true);
		  }
		 //SageInterface::setStatic(heightDecl);
		// SageInterface::setStatic(widthDecl);
		 //SageInterface::setStatic(sliceDecl);
		 //SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("height__"+varname,firstFuncDecl->get_scope()),heightExpr),true);
		 //SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("width__"+varname,firstFuncDecl->get_scope()),widthExpr),true);
		 //SageInterface::insertStatementBefore(varDecl,buildAssignStatement(buildVarRefExp("slice__"+varname,firstFuncDecl->get_scope()),sliceExpr),true);
		 createMallocPtrStmt(varname,type->findBaseType(),storeDim.size()-1,varDeclScope,varDecl);
		 SageInterface::removeStatement(varDecl);
		}
	}
}
}
}



bool Linearize::findVarDecl(string name,SgBasicBlock *block,SgVariableDeclaration **varDecl)
{
	bool contain=false;
	ROSE_ASSERT(isSgBasicBlock(block)!=NULL);
	Rose_STL_Container<SgNode*> varDeclList=NodeQuery::querySubTree(block,V_SgVariableDeclaration);
	for(Rose_STL_Container<SgNode*>::iterator it=varDeclList.begin();it!=varDeclList.end();it++)
	{
		SgVariableDeclaration *var_decl=isSgVariableDeclaration(*it);
		ROSE_ASSERT(varDecl!=NULL);
		string varname=SageInterface::get_name(var_decl);
		if(varname.compare(name)==0)
		{
			*varDecl=var_decl;
			contain=true;
			break;
		}
	}
	return contain;
}


void Linearize::linearizeArrayReferences(SgNode *node)
{
Rose_STL_Container<SgNode*> arrRefList=NodeQuery::querySubTree(node,V_SgPntrArrRefExp);
for(Rose_STL_Container<SgNode*>::iterator it=arrRefList.begin();it!=arrRefList.end();it++)
{
	SgPntrArrRefExp *arrRef=isSgPntrArrRefExp(*it);
        if(arrRef==NULL)continue;
        SgInitializedName *iname=SageInterface::convertRefToInitializedName(arrRef);
	if(isSgArrayType(iname->get_type())==NULL)continue;
	string name=iname->get_name();
	SgType *type=iname->get_type();
	SgExpression *arrayName;
	vector<SgExpression*> subscripts;
	bool checkArray=isArrayReference(arrRef,&arrayName,&subscripts);
	assert(checkArray);
	int dim=subscripts.size();
//	int dim=subscripts.size();//This variable is required as insert does take function call
//	arrnamedimmap.insert({name,dim});
//	//cout<<arrRef->unparseToString()<<"  "<<arrRef->get_file_info()->isCompilerGenerated()<<endl;
//	//cout<<type->unparseToString()<<endl;
//	//auto checkDim=arrnamedimmap.find(name);
//	//if(checkDim!=arrnamedimmap.end()&&checkDim->second!=subscripts.size())
//     //continue;
        if(arrNameDimInfo[name] > 3)
	continue;
	if(subscripts.size()==2)
	{
		SgExpression *subW_expr=SageInterface::copyExpression(subscripts.at(0));
		SgExpression *subH_expr=SageInterface::copyExpression(subscripts.at(1));
		string width="width_"+name;
		string widthName=(uniqNames.find(width))->second;
		SgVarRefExp  *width_expr=buildVarRefExp(SgName(widthName));
		SgExpression *newArrIndexExpr=buildAddOp(buildMultiplyOp(subH_expr,width_expr),subW_expr);
		SgPntrArrRefExp *newArrRefExp=buildPntrArrRefExp(SageInterface::deepCopy(buildVarRefExp(SgName(name),iname->get_scope())),newArrIndexExpr);
		SageInterface::replaceExpression(arrRef, newArrRefExp);
	}
	else if(subscripts.size()==3)
	{
		SgExpression *subW_expr=SageInterface::copyExpression(subscripts.at(0));
		SgExpression *subH_expr=SageInterface::copyExpression(subscripts.at(1));
		SgExpression *subS_expr=SageInterface::copyExpression(subscripts.at(2));
		string width="width_"+name;
                string widthName=(uniqNames.find(width))->second;
		SgVarRefExp  *width_expr=buildVarRefExp(SgName(widthName));
		string height="height_"+name;
                string heightName=(uniqNames.find(height))->second;
		SgVarRefExp  *height_expr=buildVarRefExp(SgName(heightName));
		SgExpression *newArrIndexExpr=buildAddOp(subW_expr,buildAddOp(buildMultiplyOp(subH_expr,width_expr),buildMultiplyOp(subS_expr, buildMultiplyOp(width_expr,height_expr))));
		SgPntrArrRefExp *newArrRefExp=buildPntrArrRefExp(SageInterface::deepCopy(buildVarRefExp(SgName(name),iname->get_scope())),newArrIndexExpr);
		SageInterface::replaceExpression(arrRef, newArrRefExp);
	}
}
}

void Linearize::convertParamArrToPointer(SgNode *node)
{
	SgFunctionDeclaration *mainFuncDecl=NULL;
	Rose_STL_Container<SgNode*> funcDeclList=NodeQuery::querySubTree(node,V_SgFunctionDeclaration);
	for(Rose_STL_Container<SgNode*>::iterator it=funcDeclList.begin();it!=funcDeclList.end();it++)
	{
		SgFunctionDeclaration *funcDecl=isSgFunctionDeclaration(*it);
		ROSE_ASSERT(funcDecl!=NULL);
		map<string,vector<SgExpression*>> arrNameDimMap;
		if(funcDecl->get_file_info()->isSameFile(isSgFile(node)))
		{
			string name=funcDecl->get_name();
			if(name.compare("main")==0){mainFuncDecl=funcDecl;continue;}
			//cout<<"Function Name:- "<<name<<endl;
			SgFunctionParameterList *newfuncParamList=SageBuilder::buildFunctionParameterList();
			SgFunctionParameterList *funcParamList=funcDecl->get_parameterList();
			SgInitializedNamePtrList &paramList=funcParamList->get_args();
			for(SgInitializedNamePtrList::iterator iter=paramList.begin();iter!=paramList.end();iter++)
			{
				SgInitializedName *piname=isSgInitializedName(*iter);
				string param_name=piname->get_name();
				SgType *param_type=piname->get_type();
				if(isSgArrayType(param_type)!=NULL)
				{
					SgInitializedName *newpiname=buildInitializedName(SgName(param_name),buildPointerType(param_type->findBaseType()));
					newfuncParamList->append_arg(newpiname);
					vector<SgExpression*> subsInfo=SageInterface::get_C_array_dimensions(param_type);
					if(funcDecl->get_definition()!=NULL && subsInfo.size()>1)
						{
							arrNameDimInfo.insert({param_name,subsInfo.size()-1});
							arrNameDimValuesInfo.insert({param_name,subsInfo});
							arrNameDimMap.insert({param_name,subsInfo});
						}
				}
				else
					newfuncParamList->append_arg(piname);
			}
			if(funcDecl->get_definition()==NULL)
			{
				SgFunctionDeclaration *newFuncDecl=buildNondefiningFunctionDeclaration(SgName(name),funcDecl->get_type()->get_orig_return_type(),newfuncParamList,funcDecl->get_scope());
				if(SageInterface::isStatic(isSgDeclarationStatement(funcDecl)))
				SageInterface::setStatic(isSgDeclarationStatement(newFuncDecl));
				SageInterface::replaceStatement(funcDecl,newFuncDecl,true);
			}
			if(funcDecl->get_definition()!=NULL)
			{
				vector<SgExpression*> subinfo;
				SgScopeStatement *scope=funcDecl->get_definition()->get_body();
				string heightUname,widthUname,sliceUname;
				for(auto it=arrNameDimMap.begin();it!=arrNameDimMap.end();it++)
				{
					subinfo=it->second;
					string arrname=it->first;
					if(subinfo.size()-1==1)
					{
					string height="height_"+arrname;
					if(uniqNames.find(height)==uniqNames.end())
					{
					heightUname=SageInterface::generateUniqueVariableName(scope,height);
				 	uniqNames.insert({height,heightUname});
					}
					SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(subinfo.at(1),buildIntType()),scope);
					SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),heightDecl);
					}
					else if(subinfo.size()-1==2)
					{
					string height="height_"+arrname;
					string width="width_"+arrname;
 					if(uniqNames.find(width)==uniqNames.end() && uniqNames.find(height)==uniqNames.end())
					{
					heightUname=SageInterface::generateUniqueVariableName(scope,height);
					widthUname=SageInterface::generateUniqueVariableName(scope,width);
					uniqNames.insert({height,heightUname});
                                        uniqNames.insert({width,widthUname});
					}
					SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(subinfo.at(1),buildIntType()),scope);
					SgVariableDeclaration *widthDecl=buildVariableDeclaration(SgName(widthUname),buildIntType(),buildAssignInitializer(subinfo.at(2),buildIntType()),scope);
					SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),heightDecl);
					SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),widthDecl);
					}
					else if(subinfo.size()-1==3)
					{
					string height="height_"+arrname;
					string width="width_"+arrname;
					string slice="slice_"+arrname;
		if(uniqNames.find(width)==uniqNames.end() && uniqNames.find(height)==uniqNames.end() && uniqNames.find(slice)==uniqNames.end())
                                        {
                                        heightUname=SageInterface::generateUniqueVariableName(scope,height);
                                        widthUname=SageInterface::generateUniqueVariableName(scope,width);
					sliceUname=SageInterface::generateUniqueVariableName(scope,slice);
					uniqNames.insert({height,heightUname});
                                        uniqNames.insert({width,widthUname});
                                        uniqNames.insert({slice,sliceUname});
					}
				SgVariableDeclaration *heightDecl=buildVariableDeclaration(SgName(heightUname),buildIntType(),buildAssignInitializer(subinfo.at(1),buildIntType()),scope);
					SgVariableDeclaration *widthDecl=buildVariableDeclaration(SgName(widthUname),buildIntType(),buildAssignInitializer(subinfo.at(2),buildIntType()),scope);
					SgVariableDeclaration *sliceDecl=buildVariableDeclaration(SgName(sliceUname),buildIntType(),buildAssignInitializer(subinfo.at(3),buildIntType()),scope);
                                        SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),heightDecl);
					SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),widthDecl);
					SageInterface::insertStatementBefore(SageInterface::getFirstStatement(scope),sliceDecl);
					}
				}
				funcDecl->set_parameterList(newfuncParamList);
			}
		}
	}
}

void Linearize::normalizeArrayInitDecl(SgFunctionDeclaration *funcDecl) {
        SgBasicBlock *bblock = isSgBasicBlock(funcDecl->get_definition()->get_body());
        Rose_STL_Container<SgNode*> varDeclList =NodeQuery::querySubTree(bblock,V_SgVariableDeclaration);
        for (Rose_STL_Container<SgNode*>::iterator iter=varDeclList.begin();iter!=varDeclList.end();iter++)
        {
                SgVariableDeclaration *varDecl=isSgVariableDeclaration(*iter);
                ROSE_ASSERT(varDecl!=NULL);
		SgStatement *locStmt=isSgStatement(varDecl);
		ROSE_ASSERT(locStmt!=NULL);
                SgInitializedName *i_name=SageInterface::getFirstInitializedName(varDecl);
                if(isSgAggregateInitializer(i_name->get_initializer()))
                {
                        std::cout<<i_name->get_name()<<std::endl;
                        std::string varname=i_name->get_name();
                        SgScopeStatement *scope=isSgScopeStatement(i_name->get_scope());
                        SgAggregateInitializer *initializer=isSgAggregateInitializer(i_name->get_initializer());
                        SgExprListExp *exprListExp=initializer->get_initializers();
                        SgExpressionPtrList &exprList=exprListExp->get_expressions();
                        SgArrayType *arrType=isSgArrayType(initializer->get_type());
                        std::vector<SgExpression*> dimInfo=SageInterface::get_C_array_dimensions(arrType);
                        int dim=SageInterface::getDimensionCount(i_name->get_type());

                        if(dim==1)
                        {
                                int colWidth=exprList.size();//isSgIntVal(dimInfo.at(1))->get_value();
                                for(int j=0;j<colWidth;++j)
                                {
                                        SgExpression *exp=isSgExpression(exprListExp->get_traversalSuccessorByIndex(j));
                                        SgExpression *copyExp=SageInterface::copyExpression(exp);
                                     SgStatement *stmt=buildAssignStatement(buildPntrArrRefExp(buildVarRefExp(varname,scope),buildIntVal(j)),copyExp);
                                        SageInterface::insertStatementAfter(locStmt,stmt) ;
					locStmt=stmt;
                                }
                        }
                        else if(dim==2)
                        {
                                int rowWidth=exprList.size();//isSgIntVal(dimInfo.at(1))->get_value();
                                //int colWidth=isSgIntVal(dimInfo.at(2))->get_value();
                                for(int j=0;j<rowWidth;j++)
                                {
                                        SgAggregateInitializer *aggInit=isSgAggregateInitializer(exprListExp->get_traversalSuccessorByIndex(j));
                                        SgExprListExp *expList=aggInit->get_initializers();
			                SgExpressionPtrList &eList=expList->get_expressions();
					int colWidth=eList.size();
                                        for(int k=0;k<colWidth;++k)
                                        {
                                        SgExpression *exp=isSgExpression(expList->get_traversalSuccessorByIndex(k));
                                        SgExpression *copyExp=SageInterface::copyExpression(exp);
                                        SgStatement *stmt=buildAssignStatement(buildPntrArrRefExp(buildPntrArrRefExp(buildVarRefExp(varname,scope),buildIntVal(j)),buildIntVal(k)),copyExp);
                                        SageInterface::insertStatementAfter(locStmt,stmt);
					locStmt=stmt;
                                        }
					
                                }
                        }
                        else if(dim==3)
                        {

                                int rowWidth=exprList.size();//isSgIntVal(dimInfo.at(1))->get_value(); 
                                //int colWidth=isSgIntVal(dimInfo.at(2))->get_value();
                                //int heightWidth=isSgIntVal(dimInfo.at(3))->get_value();
                                for(int j=0;j<rowWidth;j++)
                                {
                                        SgAggregateInitializer *aggInit=isSgAggregateInitializer(exprListExp->get_traversalSuccessorByIndex(j));
                                        SgExprListExp *expList=aggInit->get_initializers();
					SgExpressionPtrList &eList=expList->get_expressions();
                                        int colWidth=eList.size();
					for(int k=0;k<colWidth;k++)
                                        {
                                                SgAggregateInitializer *aggInit1=isSgAggregateInitializer(expList->get_traversalSuccessorByIndex(k));
                                                SgExprListExp *expList1=aggInit1->get_initializers();
						SgExpressionPtrList &eList1=expList1->get_expressions();
                                                int heightWidth=eList1.size();
                                                for(int l=0;l<heightWidth;++l)
                                                {
                                                        SgExpression *exp=isSgExpression(expList1->get_traversalSuccessorByIndex(l));
                                                        SgExpression *copyExp=SageInterface::copyExpression(exp);
                                                        SgStatement *stmt=buildAssignStatement(buildPntrArrRefExp(buildPntrArrRefExp(buildPntrArrRefExp(buildVarRefExp(varname,scope),buildIntVal(j)),buildIntVal(k)),buildIntVal(l)),copyExp);
                                                        SageInterface::insertStatementAfter(locStmt,stmt);
							locStmt=stmt;
                                                }
                                        }
                                }
                        }
                        SgStatement *newVarDeclStmt=buildVariableDeclaration(SgName(varname),i_name->get_type(),NULL,scope);
                        SageInterface::replaceStatement(varDecl,newVarDeclStmt);
                }
        }
}


void Linearize::doNormalization(SgNode *node) {
	Rose_STL_Container<SgNode*> funcDeclList=NodeQuery::querySubTree(node,V_SgFunctionDeclaration);
	for(Rose_STL_Container<SgNode*>::iterator iter=funcDeclList.begin();iter!=funcDeclList.end();iter++)
	{
		SgFunctionDeclaration *funcDecl=isSgFunctionDeclaration(*iter);
		ROSE_ASSERT(funcDecl!=NULL);
		if(funcDecl->get_file_info()->isSameFile(isSgFile(node))==true &&funcDecl->get_definition()!=NULL) {
			normalizeArrayInitDecl(funcDecl);
		}
	}
}

void Linearize::linearize(SgFile *sfile)
{
SgProject *project=SageInterface::getProject();
SimpleInstrumentation instObj;
instObj.traverseInputFiles(project,preorder);
SageInterface::cutPreprocessingInfo(locatedNode,PreprocessingInfo::before,saveBuff);

SgFunctionDeclaration *mainDecl=SageInterface::findMain(sfile);
mainBodyScope=mainDecl->get_definition()->get_body()->get_scope();
firstMainBodyStmt=SageInterface::getFirstStatement(mainBodyScope);

doNormalization(sfile);
convertToPointerArray(sfile);//convert Array Declarations to pointer array
convertParamArrToPointer(sfile);//convert Parameter Array in function Definition into Pointer array
linearizeArrayReferences(sfile);//convert 2d and 3d array references into 1d

flag=false;
instObj.traverseInputFiles(project,preorder);
SageInterface::insertHeader(isSgSourceFile(sfile),"stdlib.h",true,true);
SageInterface::pastePreprocessingInfo(locatedNode,PreprocessingInfo::before,saveBuff);

SageInterface::fixVariableReferences(sfile);
}





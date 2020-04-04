/*
 * This header file is being written to store the dimensions of an array according
 * to their names.
 * This is a global static field static map<std::string,int>arrNameDimInfo;
 */
//#ifndef ARRNAMEDIM_H_
//#define ARRNAMEDIM_H_
#include <iostream>
#include "rose.h"

using namespace SageBuilder;

static std::map<std::string,int> arrNameDimInfo;
static std::map<std::string,std::vector<SgExpression*> > arrNameDimValuesInfo;

int findDimAccName(std::string name)
{
int dim;
auto it=arrNameDimInfo.find(name);
dim=it->second;
return dim;
}

std::vector<SgExpression*> findDimValuesAccName(std::string name)
{
std::vector<SgExpression*> dimValues;
auto it=arrNameDimValuesInfo.find(name);
dimValues=it->second;
return dimValues;
}


/*
 *  *  * This Function Should only be used for functions only
 *   *   * This Function will check whether a variable is declared in the function body
 *    *    * if declared then it will not do anything otherwise it will declare that variable as first statement 
 *     *     * in the function body
 *      *      */
void findAndFixVarDecl(std::string name,SgBasicBlock *block,SgType *type,SgAssignInitializer *assignInit)
{
        bool contain=false;
        ROSE_ASSERT(isSgBasicBlock(block)!=NULL);
        Rose_STL_Container<SgNode*> varDeclList=NodeQuery::querySubTree(block,V_SgVariableDeclaration);
        for(Rose_STL_Container<SgNode*>::iterator it=varDeclList.begin();it!=varDeclList.end();it++)
        {
                SgVariableDeclaration *varDecl=isSgVariableDeclaration(*it);
                ROSE_ASSERT(varDecl!=NULL);
                SgInitializedName *iname=SageInterface::getFirstInitializedName(varDecl);
                std::string varname=iname->get_name();
                if(varname.compare(name)==0)
                {
                        contain=true;
                        break;
                }
        }
        /*Variable Declaration Not Found In the basic block of function body*/
        if(!contain)
        {
        SgStatement *firstStmt=SageInterface::getFirstStatement(block);
        SgStatement *stmt=buildVariableDeclaration(SgName(name),type,assignInit,block);
        SageInterface::insertStatementBefore(firstStmt,stmt);
        }
}



//#endif

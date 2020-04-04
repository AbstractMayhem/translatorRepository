#ifndef  LINEARIZEARRAY_H
#define  LINEARIZEARRAY_H

#include <rose.h>
class SimpleInstrumentation : public AstSimpleProcessing
{
public:
virtual void visit(SgNode *node);
};

class Linearize
{
public:
void createMallocPtrStmt(std::string name,SgType *type,int dim,SgScopeStatement *scope,SgVariableDeclaration *targetDecl);

SgFunctionDeclaration* getFirstFunctionDeclaration(SgNode *node);

void convertToPointerArray(SgNode *node);

bool findVarDecl(std::string name,SgBasicBlock *block,SgVariableDeclaration **varDecl);

void linearizeArrayReferences(SgNode *node);

void convertParamArrToPointer(SgNode *node);

void normalizeArrayInitDecl(SgFunctionDeclaration *funcDecl);

void doNormalization(SgNode *node);

void linearize(SgFile *sfile);
};

#endif

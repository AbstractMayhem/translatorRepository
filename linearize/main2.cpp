#include <rose.h>
#include "Linearize.h"
#include "constantFolding.h"

using namespace SageBuilder;

int main(int argc,char *argv[]){
ROSE_INITIALIZE;
SgProject *project=frontend(argc,argv);
ROSE_ASSERT(project!=NULL);
SgSourceFile *sfile=isSgSourceFile(project->get_fileList()[0]);
ROSE_ASSERT(sfile!=NULL);
Linearize lin;
lin.linearize(sfile);

//AstTests::runAllTests(project);
ConstantFolding::constantFoldingOptimization(project);
//ConstantFolding::constantUnFoldingTest(project);
//ConstantFolding::constantFoldingOptimization(project);

project->unparse();
return 0;
}

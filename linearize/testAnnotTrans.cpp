#include <iostream>
#include <rose.h>
#include <fstream>
#include <string>
#define RSTL Rose_STL_Container<SgNode*>

using namespace std;

int appendToAnnotFile(std::string info){
std::fstream new_file;
new_file.open("new_file.txt",std::ios::out | std::ios::app);
if(!new_file)
{
std::cout<<"No such File"<<std::endl;
return -1;
}
else
{
//string info = "Insert Text Here!!!";
new_file<<info<<std::endl;
new_file.close();
}
}

int main(int argc,char *argv[]){
ROSE_INITIALIZE;
SgProject *project=frontend(argc,argv);
ROSE_ASSERT(project!=NULL);
SgSourceFile *sfile=isSgSourceFile(project->get_fileList()[0]);
ROSE_ASSERT(sfile!=NULL);
RSTL funcExpList=NodeQuery::querySubTree(sfile,V_SgFunctionCallExp);
RSTL::iterator iter;
for(iter=funcExpList.begin();iter!=funcExpList.end();++iter)
{
  SgFunctionCallExp *fexp=isSgFunctionCallExp(*iter);
  ROSE_ASSERT(fexp!=NULL);
  //cout<<fexp->unparseToString()<<endl;
  string fname=fexp->getAssociatedFunctionDeclaration()->get_name();
  SgFunctionDeclaration *funcDecl=SageInterface::findFunctionDeclaration(sfile,fname,sfile->get_globalScope(),false);    
  if(funcDecl!=NULL && funcDecl->get_file_info()->isSameFile(isSgFile(sfile)))
  {
  cout<<fname<<endl;
  cout<<funcDecl<<endl;
  cout<<funcDecl->unparseToString()<<endl;
  RSTL forLoopList=NodeQuery::querySubTree(funcDecl,V_SgForStatement);
  if(forLoopList.size()>0)
    {
        cout<<"For Loops Are Present Here. So Skipping"<<endl;
    }
    else{
    	string funcSign=fexp->getAssociatedFunctionDeclaration()->get_name();
        funcSign="operator  "+funcSign+"(";
        if(funcDecl->get_args().size()>0)
        {
          SgInitializedNamePtrList &ptrList=funcDecl->get_args();
          for(SgInitializedNamePtrList::iterator it=ptrList.begin();it!=ptrList.end();++it)
          {
                   SgInitializedName *argi_name=(*it);
                   cout<<argi_name->unparseToString()<<endl;
                   funcSign+=argi_name->get_type()->unparseToString()+" "+argi_name->get_name();
                   if(it+1!=ptrList.end())
                   funcSign+=",";
          }
         funcSign+=")"; 
	cout<<funcSign<<endl;
        funcSign+="\n{\nmodify none; read{";
          for(SgInitializedNamePtrList::iterator it=ptrList.begin();it!=ptrList.end();++it)
          {
                   SgInitializedName *argi_name=(*it);
                   cout<<argi_name->unparseToString()<<endl;
                   funcSign+=argi_name->get_name();
                   if(it+1!=ptrList.end())
                   funcSign+=",";

          }
         funcSign+="}; alias none;\n}";	
        }
    	else
    	{
          funcSign+=")\n{\nmodify none; read none; alias none;\n}";
    	}
        cout<<funcSign<<endl;
        appendToAnnotFile(funcSign);
    }
  }
}

return 0;
}



g++ -g -std=c++11  autoPar.C autoParSupport.C autoParSupport.h -I$ROSE_INC -L$ROSE_LIB -I$BOOST_INC -L$BOOST_LIB -lrose -lboost_system -pthread -o autoParTrans 


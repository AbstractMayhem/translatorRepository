/* rose_config.h.  Generated from rose_config.h.in by configure.  */
/* rose_config.h.in.  Generated from configure.ac by autoheader.  */

/* Define if building universal (internal helper macro) */
/* #undef AC_APPLE_UNIVERSAL_BUILD */

/* Absolute path of the ATERM installation bin directory */
#define ATERM_BIN_PATH ""

/* Absolute path of the ATERM installation */
#define ATERM_INSTALL_PATH ""

/* Absolute path of the ATERM installation lib directory */
#define ATERM_LIBRARY_PATH ""

/* Name of backend Ada compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_ADA_COMPILER_NAME_WITH_PATH "gnat"

/* Name of backend Cobol compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_COBOL_COMPILER_NAME_WITH_PATH "cobc"

/* Name of backend Csharp compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_CSHARP_COMPILER_NAME_WITH_PATH "mcs"

/* Major version number of backend C++ compiler. */
#define BACKEND_CXX_COMPILER_MAJOR_VERSION_NUMBER 4

/* Minor version number of backend C++ compiler. */
#define BACKEND_CXX_COMPILER_MINOR_VERSION_NUMBER 8

/* Name of backend C++ compiler excluding path (used to select code generation
   options). */
#define BACKEND_CXX_COMPILER_NAME_WITHOUT_PATH "g++"

/* Name of backend C++ compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_CXX_COMPILER_NAME_WITH_PATH "g++"

/* Is this a Clang compiler being used to compile ROSE generated code */
/* #undef BACKEND_CXX_IS_CLANG_COMPILER */

/* Is this a GNU compiler being used to compile ROSE generated code */
#define BACKEND_CXX_IS_GNU_COMPILER 1

/* Is this an Intel compiler being used to compile ROSE generated code */
/* #undef BACKEND_CXX_IS_INTEL_COMPILER */

/* Name of backend C compiler excluding path (used to select code generation
   options). */
#define BACKEND_C_COMPILER_NAME_WITHOUT_PATH "gcc"

/* Name of backend C compiler including path (may or may not explicit include
   path; used to call backend). */
#define BACKEND_C_COMPILER_NAME_WITH_PATH "gcc"

/* The backend C compiler might not support asm and might require __asm__
   instead (e.g. GNU gcc). */
/* #undef BACKEND_C_COMPILER_SUPPORTS_ASM */

/* The backend C compiler might not support asm and might require __asm__
   instead (e.g. GNU gcc). */
/* #undef BACKEND_C_COMPILER_SUPPORTS_LONG_STRING_ASM */

/* The backend C compiler might not support asm and might require __asm__
   instead (e.g. GNU gcc). */
#define BACKEND_C_COMPILER_SUPPORTS_UNDESCORE_ASM 1

/* Major version number of backend Fortran compiler. */
#define BACKEND_FORTRAN_COMPILER_MAJOR_VERSION_NUMBER 4

/* Minor version number of backend Fortran compiler. */
#define BACKEND_FORTRAN_COMPILER_MINOR_VERSION_NUMBER 8

/* Name of backend Fortran compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_FORTRAN_COMPILER_NAME_WITH_PATH "gfortran"

/* Name of backend Java compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_JAVA_COMPILER_NAME_WITH_PATH "javac"

/* Name of backend Jovial compiler including path (may or may not explicit
   include path; used to call backend). */
#define BACKEND_JOVIAL_COMPILER_NAME_WITH_PATH "default_jovial_compiler"

/* Path to the backend python interpreter */
#define BACKEND_PYTHON_INTERPRETER_NAME_WITH_PATH "/bin/python"

/* Name of backend X10 compiler, including path */
#define BACKEND_X10_COMPILER_NAME_WITH_PATH "x10c"

/* Internal EDG specific consistency tests. */
#define CHECKING 1

/* Absolute path of the COBPT installation */
#define COBPT_INSTALL_PATH ""

/* Absolute path of the COBPT installation lib directory */
#define COBPT_LIBRARY_PATH ""

/* Always defined and used for checking whether global CPP namespace is
   polluted */
#define CONFIG_ROSE 1

/* CUDA binaries directory */
/* #undef CUDA_BIN_DIR */

/* CUDA include directory */
#define CUDA_INC_DIR "/usr/local/capc/ROSE_BUILD/include-staging/cuda_HEADERS/cuda-7.5/targets/x86_64-linux/include/"

/* CUDA libraries directory */
/* #undef CUDA_LIB_DIR */

/* Include path for backend C++ compiler. */
#define CXX_INCLUDE_STRING {"g++_HEADERS", "g++_HEADERS/hdrs", "g++_HEADERS/hdrs1", "g++_HEADERS/hdrs2", "/usr/lib/gcc/x86_64-redhat-linux/4.8.5/../../../../include/c++/4.8.5", "/usr/lib/gcc/x86_64-redhat-linux/4.8.5/../../../../include/c++/4.8.5/x86_64-redhat-linux", "/usr/lib/gcc/x86_64-redhat-linux/4.8.5/../../../../include/c++/4.8.5/backward", "/usr/lib/gcc/x86_64-redhat-linux/4.8.5/include", "/usr/local/include",  "/usr/include"}

/* Is this the ROSE Analizer (part of tests to compile ROSE for analysis only
   using ROSE) */
/* #undef CXX_IS_ROSE_ANALYSIS */

/* Is this the ROSE AST File IO (part of tests to compile ROSE for AST File IO
   only using ROSE) */
/* #undef CXX_IS_ROSE_AST_FILE_IO */

/* Is this the ROSE Code Generator (part of tests to compile ROSE and generate
   code using ROSE) */
/* #undef CXX_IS_ROSE_CODE_GENERATION */

/* Is this the ROSE translator (part of tests to compile ROSE using ROSE) */
/* #undef CXX_IS_ROSE_TRANSLATOR */

/* -D options to hand to EDG C++ front-end. */
#define CXX_SPEC_DEF {"-D__GNUG__=4", "-D__GNUC__=4", "-D__GNUC_MINOR__=8", "-D__GNUC_PATCHLEVEL__=5", "--preinclude", "rose_edg_required_macros_and_functions.h"}

/* Include path for backend C compiler. */
#define C_INCLUDE_STRING {"gcc_HEADERS", "gcc_HEADERS/hdrs", "/usr/lib/gcc/x86_64-redhat-linux/4.8.5/include", "/usr/local/include",  "/usr/include"}

/* Location (unquoted) of the GCC 4.4's GOMP OpenMP runtime library. */
/* #undef GCC_GOMP_OPENMP_LIB_PATH */

/* Define to 1 if you have the `argz_add' function. */
#define HAVE_ARGZ_ADD 1

/* Define to 1 if you have the `argz_append' function. */
#define HAVE_ARGZ_APPEND 1

/* Define to 1 if you have the `argz_count' function. */
#define HAVE_ARGZ_COUNT 1

/* Define to 1 if you have the `argz_create_sep' function. */
#define HAVE_ARGZ_CREATE_SEP 1

/* Define to 1 if you have the <argz.h> header file. */
#define HAVE_ARGZ_H 1

/* Define to 1 if you have the `argz_insert' function. */
#define HAVE_ARGZ_INSERT 1

/* Define to 1 if you have the `argz_next' function. */
#define HAVE_ARGZ_NEXT 1

/* Define to 1 if you have the `argz_stringify' function. */
#define HAVE_ARGZ_STRINGIFY 1

/* Define to 1 if you have the <asm/ldt.h> header file. */
#define HAVE_ASM_LDT_H 1

/* define if the Boost library is available */
#define HAVE_BOOST /**/

/* define if the Boost::Chrono library is available */
#define HAVE_BOOST_CHRONO /**/

/* define if the Boost::Date_Time library is available */
#define HAVE_BOOST_DATE_TIME /**/

/* define if the Boost::Filesystem library is available */
#define HAVE_BOOST_FILESYSTEM /**/

/* define if the Boost::IOStreams library is available */
#define HAVE_BOOST_IOSTREAMS /**/

/* define if the Boost::PROGRAM_OPTIONS library is available */
#define HAVE_BOOST_PROGRAM_OPTIONS /**/

/* define if the Boost::Random library is available */
#define HAVE_BOOST_RANDOM /**/

/* define if the Boost::Regex library is available */
#define HAVE_BOOST_REGEX /**/

/* define if the boost::serialization headers are available */
#define HAVE_BOOST_SERIALIZATION /**/

/* define if the libboost_serialization is available */
#define HAVE_BOOST_SERIALIZATION_LIB /**/

/* define if the Boost::System library is available */
#define HAVE_BOOST_SYSTEM /**/

/* define if the Boost::Thread library is available */
#define HAVE_BOOST_THREAD /**/

/* define if the Boost::Wave library is available */
#define HAVE_BOOST_WAVE /**/

/* Define to 1 if you have the <byteswap.h> header file. */
#define HAVE_BYTESWAP_H 1

/* Define to 1 if you have the `clock_gettime' function. */
#define HAVE_CLOCK_GETTIME 1

/* Define to 1 if you have the `closedir' function. */
#define HAVE_CLOSEDIR 1

/* define if the compiler supports basic C++11 syntax */
#define HAVE_CXX11 1

/* define if the compiler supports basic C++14 syntax */
/* #undef HAVE_CXX14 */

/* Define to 1 if you have the <c_asm.h> header file. */
/* #undef HAVE_C_ASM_H */

/* Define to 1 if you have the declaration of `cygwin_conv_path', and to 0 if
   you don't. */
/* #undef HAVE_DECL_CYGWIN_CONV_PATH */

/* Define to 1 if you have the <dirent.h> header file, and it defines `DIR'.
   */
#define HAVE_DIRENT_H 1

/* Whether <dlfcn.h> and -ldl contain dladdr() */
#define HAVE_DLADDR /**/

/* Define if you have the GNU dld library. */
/* #undef HAVE_DLD */

/* Define to 1 if you have the <dld.h> header file. */
/* #undef HAVE_DLD_H */

/* Define to 1 if you have the `dlerror' function. */
#define HAVE_DLERROR 1

/* Define to 1 if you have the <dlfcn.h> header file. */
#define HAVE_DLFCN_H 1

/* Define to 1 if you have the <dl.h> header file. */
/* #undef HAVE_DL_H */

/* Define to 1 if you don't have `vprintf' but do have `_doprnt.' */
/* #undef HAVE_DOPRNT */

/* Define if you have the _dyld_func_lookup function. */
/* #undef HAVE_DYLD */

/* Define to 1 if you have the <elf.h> header file. */
#define HAVE_ELF_H 1

/* Define to 1 if the system has the type `error_t'. */
#define HAVE_ERROR_T 1

/* Use explicit template instantiation. */
#define HAVE_EXPLICIT_TEMPLATE_INSTANTIATION /**/

/* Define to 1 if you have the <ffi.h> header file. */
#define HAVE_FFI_H 1

/* Define to 1 if you have the `getcwd' function. */
#define HAVE_GETCWD 1

/* Define to 1 if you have the `gethrtime' function. */
/* #undef HAVE_GETHRTIME */

/* Define to 1 if you have the `getpagesize' function. */
#define HAVE_GETPAGESIZE 1

/* Define to 1 if you have the `getwd' function. */
#define HAVE_GETWD 1

/* Define to 1 if you have the <grp.h> header file. */
#define HAVE_GRP_H 1

/* Define to 1 if hrtime_t is defined in <sys/time.h> */
/* #undef HAVE_HRTIME_T */

/* Define to 1 if you have the <intrinsics.h> header file. */
/* #undef HAVE_INTRINSICS_H */

/* Define to 1 if you have the <inttypes.h> header file. */
#define HAVE_INTTYPES_H 1

/* Define to 1 if you have the <jni.h> header file. */
/* #undef HAVE_JNI_H */

/* Define to 1 if you have the `dl' library (-ldl). */
#define HAVE_LIBDL 1

/* Define if libdlloader will be built on this platform */
#define HAVE_LIBDLLOADER 1

/* Define to 1 if you have the <limits.h> header file. */
#define HAVE_LIMITS_H 1

/* Define to 1 if you have the <linux/dirent.h> header file. */
/* #undef HAVE_LINUX_DIRENT_H */

/* Define to 1 if you have the <linux/types.h> header file. */
#define HAVE_LINUX_TYPES_H 1

/* Define to 1 if you have the <linux/unistd.h> header file. */
#define HAVE_LINUX_UNISTD_H 1

/* Define to 1 if the type `long double' works and has more range or precision
   than `double'. */
#define HAVE_LONG_DOUBLE 1

/* Define to 1 if the type `long double' works and has more range or precision
   than `double'. */
#define HAVE_LONG_DOUBLE_WIDER 1

/* Define this if a modern libltdl is already installed */
#define HAVE_LTDL 1

/* Define to 1 if you have the <machine/endian.h> header file. */
/* #undef HAVE_MACHINE_ENDIAN_H */

/* Define to 1 if you have the `mach_absolute_time' function. */
/* #undef HAVE_MACH_ABSOLUTE_TIME */

/* Define to 1 if you have the <mach/mach_time.h> header file. */
/* #undef HAVE_MACH_MACH_TIME_H */

/* Define to 1 if you have the <mach-o/dyld.h> header file. */
/* #undef HAVE_MACH_O_DYLD_H */

/* Define to 1 if you have the <memory.h> header file. */
#define HAVE_MEMORY_H 1

/* Define to 1 if you have the `mktime' function. */
#define HAVE_MKTIME 1

/* Define to 1 if you have a working `mmap' system call. */
#define HAVE_MMAP 1

/* Define to 1 if you have MPI libs and headers. */
/* #undef HAVE_MPI */

/* Define to 1 if MySQL libraries are available */
/* #undef HAVE_MYSQL */

/* Define to 1 if you have the <ndir.h> header file, and it defines `DIR'. */
/* #undef HAVE_NDIR_H */

/* Support for libnuma a NUMA memory allocation library for many-core
   optimizations */
#define HAVE_NUMA_H /**/

/* Define to 1 if you have the `opendir' function. */
#define HAVE_OPENDIR 1

/* Define to 1 if you have the `pipe2' function. */
#define HAVE_PIPE2 1

/* Define if libtool can extract symbol lists from object files. */
#define HAVE_PRELOADED_SYMBOLS 1

/* Define to 1 if you have the <pthread.h> header file. */
#define HAVE_PTHREAD_H 1

/* If available, contains the Python version number currently in use. */
#define HAVE_PYTHON "2.7"

/* Define to 1 if you have the `readdir' function. */
#define HAVE_READDIR 1

/* Define to 1 if you have the `read_real_time' function. */
/* #undef HAVE_READ_REAL_TIME */

/* Define if you have the shl_load function. */
/* #undef HAVE_SHL_LOAD */

/* Define to 1 if you have SPOT libs and headers. */
/* #undef HAVE_SPOT */

/* Have the SQLITE3 library */
/* #undef HAVE_SQLITE3 */

/* Define to 1 if you have the <stdint.h> header file. */
#define HAVE_STDINT_H 1

/* Define to 1 if you have the <stdlib.h> header file. */
#define HAVE_STDLIB_H 1

/* Define to 1 if you have the `strcoll' function and it is properly defined.
   */
#define HAVE_STRCOLL 1

/* Define to 1 if you have the `strcspn' function. */
#define HAVE_STRCSPN 1

/* Define to 1 if you have the `strerror' function. */
#define HAVE_STRERROR 1

/* Define to 1 if you have the `strftime' function. */
#define HAVE_STRFTIME 1

/* Define to 1 if you have the <strings.h> header file. */
#define HAVE_STRINGS_H 1

/* Define to 1 if you have the <string.h> header file. */
#define HAVE_STRING_H 1

/* Define to 1 if you have the `strlcat' function. */
/* #undef HAVE_STRLCAT */

/* Define to 1 if you have the `strlcpy' function. */
/* #undef HAVE_STRLCPY */

/* Define to 1 if you have the `strspn' function. */
#define HAVE_STRSPN 1

/* Define to 1 if you have the `strstr' function. */
#define HAVE_STRSTR 1

/* Define to 1 if you have the `strtod' function. */
#define HAVE_STRTOD 1

/* Define to 1 if you have the `strtol' function. */
#define HAVE_STRTOL 1

/* Define to 1 if you have the `strtoul' function. */
#define HAVE_STRTOUL 1

/* Define to 1 if you have the <syscall.h> header file. */
#define HAVE_SYSCALL_H 1

/* Define to 1 if you have the <sys/dir.h> header file, and it defines `DIR'.
   */
/* #undef HAVE_SYS_DIR_H */

/* Define to 1 if you have the <sys/dl.h> header file. */
/* #undef HAVE_SYS_DL_H */

/* Define to 1 if you have the <sys/ioctl.h> header file. */
#define HAVE_SYS_IOCTL_H 1

/* Define to 1 if you have the <sys/mman.h> header file. */
#define HAVE_SYS_MMAN_H 1

/* Define to 1 if you have the <sys/ndir.h> header file, and it defines `DIR'.
   */
/* #undef HAVE_SYS_NDIR_H */

/* Define to 1 if you have the <sys/param.h> header file. */
#define HAVE_SYS_PARAM_H 1

/* Define to 1 if you have the <sys/socket.h> header file. */
#define HAVE_SYS_SOCKET_H 1

/* Define to 1 if you have the <sys/stat.h> header file. */
#define HAVE_SYS_STAT_H 1

/* Define to 1 if you have the <sys/sysinfo.h> header file. */
#define HAVE_SYS_SYSINFO_H 1

/* Define to 1 if you have the <sys/time.h> header file. */
#define HAVE_SYS_TIME_H 1

/* Define to 1 if you have the <sys/types.h> header file. */
#define HAVE_SYS_TYPES_H 1

/* Define to 1 if you have the <sys/uio.h> header file. */
#define HAVE_SYS_UIO_H 1

/* Define to 1 if you have the <sys/utsname.h> header file. */
#define HAVE_SYS_UTSNAME_H 1

/* Define to 1 if you have the <sys/wait.h> header file. */
#define HAVE_SYS_WAIT_H 1

/* Define to 1 if you have the <termios.h> header file. */
#define HAVE_TERMIOS_H 1

/* Define to 1 if you have the `time_base_to_time' function. */
/* #undef HAVE_TIME_BASE_TO_TIME */

/* Define to 1 if you have the <unistd.h> header file. */
#define HAVE_UNISTD_H 1

/* Defined if the user_desc type is declared in <asm/ldt.h> */
#define HAVE_USER_DESC /**/

/* Define to 1 if you have the `vprintf' function. */
#define HAVE_VPRINTF 1

/* This value is set to 1 to indicate that the system argz facility works */
#define HAVE_WORKING_ARGZ 1

/* Define to 1 if you have Z3 libs and headers. */
/* #undef HAVE_Z3 */

/* Define if you have the UNICOS _rtc() intrinsic. */
/* #undef HAVE__RTC */

/* Prefix path for use of IDA. */
/* #undef IDA_PRO_PATH */

/* Path to JVM executable */
#define JAVA_JVM_PATH "/usr/java/jdk1.8.0_191/bin/java"

/* Major version number of the Java JDK */
#define JAVA_VERSION_MAJOR "1"

/* Minor version number of the Java JDK */
#define JAVA_VERSION_MINOR "8"

/* Patch version number of the Java JDK */
#define JAVA_VERSION_PATCH "0"

/* Release version number of the Java JDK */
#define JAVA_VERSION_RELEASE "191"

/* Define if the OS needs help to load dependent libraries for dlopen(). */
/* #undef LTDL_DLOPEN_DEPLIBS */

/* Define to the system default library search path. */
#define LT_DLSEARCH_PATH "/lib64:/usr/lib64:/lib:/usr/lib:/usr/lib64/atlas:/usr/lib64/codeblocks/wxContribItems:/usr/local/cuda-10.1/targets/x86_64-linux/lib:/usr/lib64/dyninst:/usr/lib64/iscsi:/usr/lib64/llvm:/usr/lib64/mysql:/usr/local/mpich-install/lib:/usr/lib:/usr/lib64/libglvnd:/usr/local/nsm/slurm-17.11.9-2/lib/:/usr/lib64:/usr/lib64/slurm:/usr/lib64/tcl8.5"

/* The archive extension */
#define LT_LIBEXT "a"

/* The archive prefix */
#define LT_LIBPREFIX "lib"

/* Define to the extension used for runtime loadable modules, say, ".so". */
#define LT_MODULE_EXT ".so"

/* Define to the name of the environment variable that determines the run-time
   module search path. */
#define LT_MODULE_PATH_VAR "LD_LIBRARY_PATH"

/* Define to the sub-directory in which libtool stores uninstalled libraries.
   */
#define LT_OBJDIR ".libs/"

/* Define to the shared library suffix, say, ".dylib". */
/* #undef LT_SHARED_EXT */

/* Define if dlsym() requires a leading underscore in symbol names. */
/* #undef NEED_USCORE */

/* Define to 1 if your C compiler doesn't accept -c and -o together. */
/* #undef NO_MINUS_C_MINUS_O */

/* Absolute path of the modified GNU Octave installation */
#define OCTAVE_PARSER_INSTALL_TARFILE ""

/* Location (unquoted) of the Omni OpenMP run time library. */
/* #undef OMNI_OPENMP_LIB_PATH */

/* OpenCL include directory */
/* #undef OPENCL_INC_DIR */

/* OpenCL libraries directory */
/* #undef OPENCL_LIB_DIR */

/* Name of package */
#define PACKAGE "rose"

/* Define to the address where bug reports for this package should be sent. */
#define PACKAGE_BUGREPORT ""

/* Define to the full name of this package. */
#define PACKAGE_NAME "ROSE"

/* Define to the full name and version of this package. */
#define PACKAGE_STRING "ROSE 0.9.10.54"

/* Define to the one symbol short name of this package. */
#define PACKAGE_TARNAME "rose"

/* Define to the home page for this package. */
#define PACKAGE_URL ""

/* Define to the version of this package. */
#define PACKAGE_VERSION "0.9.10.54"

/* "Version of Python selected when building ROSE." */
#define PYTHON_VERSION ($ac_python_version)

/* Define as the return type of signal handlers (`int' or `void'). */
#define RETSIGTYPE void

/* apple Operating System (OS) being used to build ROSE */
/* #undef ROSE_APPLE_OS_VENDOR */

/* Determines how failed assertions should behave. */
#define ROSE_ASSERTION_BEHAVIOR ROSE_ASSERTION_EXIT

/* Location (unquoted) of Boost specified on configure line. */
#define ROSE_BOOST_PATH "/usr/local/capc/BOOST_BUILD/"

/* Version of Boost specified on configure line. */
#define ROSE_BOOST_VERSION 106100

/* Build ROSE to support the Binary Analysis */
/* #undef ROSE_BUILD_BINARY_ANALYSIS_SUPPORT */

/* Build ROSE to support the CUDA langauge */
/* #undef ROSE_BUILD_CUDA_LANGUAGE_SUPPORT */

/* Build ROSE to support the C++ langauge */
#define ROSE_BUILD_CXX_LANGUAGE_SUPPORT /**/

/* Build ROSE to support the C langauge */
#define ROSE_BUILD_C_LANGUAGE_SUPPORT /**/

/* Build ROSE to support the Fortran langauge */
/* #undef ROSE_BUILD_FORTRAN_LANGUAGE_SUPPORT */

/* Build ROSE to support the Java langauge */
/* #undef ROSE_BUILD_JAVA_LANGUAGE_SUPPORT */

/* Build ROSE to support the OpenCL langauge */
#define ROSE_BUILD_OPENCL_LANGUAGE_SUPPORT /**/

/* Build ROSE to support the PHP langauge */
/* #undef ROSE_BUILD_PHP_LANGUAGE_SUPPORT */

/* Build ROSE projects directory */
/* #undef ROSE_BUILD_PROJECTS_DIRECTORY_SUPPORT */

/* Build ROSE to support the Python langauge */
/* #undef ROSE_BUILD_PYTHON_LANGUAGE_SUPPORT */

/* Build ROSE tests directory */
#define ROSE_BUILD_TESTS_DIRECTORY_SUPPORT /**/

/* Build ROSE tutorial directory */
#define ROSE_BUILD_TUTORIAL_DIRECTORY_SUPPORT /**/

/* Build ROSE to support the X10 langauge */
/* #undef ROSE_BUILD_X10_LANGUAGE_SUPPORT */

/* CentOS Operating System (OS) being used to build ROSE */
/* #undef ROSE_CENTOS_OS_VENDOR */

/* Location of ROSE Compile Tree. */
#define ROSE_COMPILE_TREE_PATH "/usr/local/capc/ROSE_BUILD"

/* Encapsulates some important configuration details for Rose::initialize */
#define ROSE_CONFIG_TOKEN " boost-106100 gnu-4.8 pthread"

/* Debian Operating System (OS) being used to build ROSE */
/* #undef ROSE_DEBIAN_OS_VENDOR */

/* Controls large volumes of output spew useful for debugging new ADA/ROSE
   connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_ADA_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new COBOL/ROSE
   connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_COBOL_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new CSHARP/ROSE
   connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_CSHARP_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new JOVIAL/ROSE
   connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_JOVIAL_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new
   Octave/Matlab ROSE connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_MATLAB_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new OFP/ROSE
   connection code */
/* #undef ROSE_DEBUG_EXPERIMENTAL_OFP_ROSE_CONNECTION */

/* Controls large volumes of output spew useful for debugging new EDG/ROSE
   connection code */
/* #undef ROSE_DEBUG_NEW_EDG_ROSE_CONNECTION */

/* EDG major version number */
#define ROSE_EDG_MAJOR_VERSION_NUMBER 4

/* EDG minor version number */
#define ROSE_EDG_MINOR_VERSION_NUMBER 9

/* Enables development of experimental ada frontend */
/* #undef ROSE_EXPERIMENTAL_ADA_ROSE_CONNECTION */

/* Path to GNAT Ada compiler used in development of experimental ada frontend
   */
/* #undef ROSE_EXPERIMENTAL_ADA_ROSE_CONNECTION_GNAT_HOME */

/* Enables development of experimental cobol frontend */
/* #undef ROSE_EXPERIMENTAL_COBOL_ROSE_CONNECTION */

/* Enables development of experimental csharp frontend */
/* #undef ROSE_EXPERIMENTAL_CSHARP_ROSE_CONNECTION */

/* Path to Mono Csharp compiler used in development of experimental csharp
   frontend */
/* #undef ROSE_EXPERIMENTAL_CSHARP_ROSE_CONNECTION_MONO_HOME */

/* Path to Roslyn Csharp library used in development of experimental csharp
   frontend */
/* #undef ROSE_EXPERIMENTAL_CSHARP_ROSE_CONNECTION_ROSLYN_HOME */

/* Enables development of experimental jovial frontend */
/* #undef ROSE_EXPERIMENTAL_JOVIAL_ROSE_CONNECTION */

/* Enables development of experimental Octave/Matlab frontend */
/* #undef ROSE_EXPERIMENTAL_MATLAB_ROSE_CONNECTION */

/* Enables development of experimental fortran frontend */
/* #undef ROSE_EXPERIMENTAL_OFP_ROSE_CONNECTION */

/* Defined if dlib is available. */
/* #undef ROSE_HAVE_DLIB */

/* Defined when libdwarf is available. */
/* #undef ROSE_HAVE_LIBDWARF */

/* Defined when libelf is available. */
/* #undef ROSE_HAVE_LIBELF */

/* Defined when libgcrypt is available. */
/* #undef ROSE_HAVE_LIBGCRYPT */

/* Defined when libmagic is available. */
/* #undef ROSE_HAVE_LIBMAGIC */

/* Defined if the pqxx library is available */
/* #undef ROSE_HAVE_LIBPQXX */

/* Defined if the readline library and headers are available. */
/* #undef ROSE_HAVE_LIBREADLINE */

/* Defined when libyaml-cpp is available */
/* #undef ROSE_HAVE_LIBYAML */

/* Defined when the Yices SMT-Solver library is present and should be used. */
/* #undef ROSE_HAVE_LIBYICES */

/* Define to 1 if you have Z3 libs and headers. */
/* #undef ROSE_HAVE_Z3 */

/* Location (unquoted) of the top directory path to which ROSE is installed.
   */
#define ROSE_INSTALLATION_PATH "/usr/local/capc/ROSE_BUILD"

/* OFP class path for Jave Virtual Machine */
#define ROSE_OFP_CLASSPATH /usr/local/capc/rose/src/3rdPartyLibraries/antlr-jars/antlr-3.3-complete.jar:/usr/local/capc/rose/src/3rdPartyLibraries/fortran-parser/OpenFortranParser-20111001.jar

/* OFP jar file */
#define ROSE_OFP_JAR_FILE OpenFortranParser-20111001.jar

/* OFP major version number */
#define ROSE_OFP_MAJOR_VERSION_NUMBER 0

/* OFP minor version number */
#define ROSE_OFP_MINOR_VERSION_NUMBER 8

/* OFP patch version number */
#define ROSE_OFP_PATCH_VERSION_NUMBER 3

/* OFP version number */
#define ROSE_OFP_VERSION_NUMBER 20111001

/* RedHat Operating System (OS) major release number being used to build ROSE
   */
#define ROSE_OS_MAJOR_RELEASE_NUMBER 

/* RedHat Operating System (OS) minor release number being used to build ROSE
   */
#define ROSE_OS_MINOR_RELEASE_NUMBER 

/* RedHat Operating System (OS) being used to build ROSE */
/* #undef ROSE_REDHAT_OS_VENDOR */

/* Git SCM version information for ROSE: commit identifier. */
#define ROSE_SCM_VERSION_ID "e11cc2d5cb88bc196f5c80421699132c6843bda0"

/* Git SCM version information for ROSE: commit date (Unix timestamp). */
#define ROSE_SCM_VERSION_UNIX_DATE 1530488088

/* Variable like LD_LIBRARY_PATH */
#define ROSE_SHLIBPATH_VAR "LD_LIBRARY_PATH"

/* Location of ROSE Source Tree. */
#define ROSE_SOURCE_TREE_PATH "/usr/local/capc/rose"

/* Ubuntu Operating System (OS) being used to build ROSE */
/* #undef ROSE_UBUNTU_OS_VENDOR */

/* Whether to use Candl support or not within ROSE */
/* #undef ROSE_USE_CANDL */

/* Use Clang for parsing C/C++-like languages */
/* #undef ROSE_USE_CLANG_FRONTEND */

/* Whether to use Cloog support or not within ROSE */
/* #undef ROSE_USE_CLOOG */

/* Whether to use the new EDG version 4.x */
#define ROSE_USE_EDG_VERSION_4 /**/

/* Whether to use the new EDG version 4.11 */
/* #undef ROSE_USE_EDG_VERSION_4_11 */

/* Whether to use the new EDG version 4.12 */
/* #undef ROSE_USE_EDG_VERSION_4_12 */

/* Whether to use the new EDG version 4.14 */
/* #undef ROSE_USE_EDG_VERSION_4_14 */

/* Whether to use the new EDG version 4.4 */
/* #undef ROSE_USE_EDG_VERSION_4_4 */

/* Whether to use the new EDG version 4.7 */
/* #undef ROSE_USE_EDG_VERSION_4_7 */

/* Whether to use the new EDG version 4.8 */
/* #undef ROSE_USE_EDG_VERSION_4_8 */

/* Whether to use the new EDG version 4.9 */
#define ROSE_USE_EDG_VERSION_4_9 /**/

/* Defined if Ether from Georgia Tech is available. */
/* #undef ROSE_USE_ETHER */

/* Support for a list of warnings that will be treated as errors for ROSE
   development */
/* #undef ROSE_USE_FATAL_ROSE_WARNINGS_SUPPORT */

/* Whether to use a special no-reuse mode of memory pools */
/* #undef ROSE_USE_MEMORY_POOL_NO_REUSE */

/* Controls use of Microsoft MSVC features */
/* #undef ROSE_USE_MICROSOFT_EXTENSIONS */

/* Whether to use the new interface to EDG */
#define ROSE_USE_NEW_EDG_INTERFACE /**/

/* Whether to use Parma Polyhedral Library (PPL) support or not within ROSE */
/* #undef ROSE_USE_PPL */

/* Whether to use ScopLib support or not within ROSE */
/* #undef ROSE_USE_SCOPLIB */

/* Whether to use smaller (but more numerous) generated files for the ROSE IR
   */
/* #undef ROSE_USE_SMALLER_GENERATED_FILES */

/* Support for an advanced uniform warning level for ROSE development */
/* #undef ROSE_USE_UNIFORM_ADVANCED_WARNINGS_SUPPORT */

/* Defined if the web toolkit Wt is available. */
#define ROSE_USE_WT 1

/* Whether to use the new graph IR nodes compatability option with older API
   */
/* #undef ROSE_USING_GRAPH_IR_NODES_FOR_BACKWARD_COMPATABILITY */

/* Simple preprocessor as default in ROSE */
#define ROSE_WAVE_DEFAULT false

/* Location (unquoted) of Wave specified on configure line. */
#define ROSE_WAVE_PATH "/usr/local/capc/BOOST_BUILD//wave"

/* Absolute name of yices executable, or the empty string. */
/* #undef ROSE_YICES */

/* Absolute name of z3 executable, or the empty string. */
#define ROSE_Z3 ""

/* Control use of SAGE within EDG. */
#define SAGE_TRANSFORM 1

/* The size of `char', as computed by sizeof. */
#define SIZEOF_CHAR 1

/* The size of `double', as computed by sizeof. */
#define SIZEOF_DOUBLE 8

/* The size of `float', as computed by sizeof. */
#define SIZEOF_FLOAT 4

/* The size of `int', as computed by sizeof. */
#define SIZEOF_INT 4

/* The size of `long', as computed by sizeof. */
#define SIZEOF_LONG 8

/* The size of `long double', as computed by sizeof. */
#define SIZEOF_LONG_DOUBLE 16

/* The size of `long long', as computed by sizeof. */
#define SIZEOF_LONG_LONG 8

/* The size of `short', as computed by sizeof. */
#define SIZEOF_SHORT 2

/* The size of `void *', as computed by sizeof. */
#define SIZEOF_VOID_P 8

/* Define to 1 if you have the ANSI C header files. */
#define STDC_HEADERS 1

/* Absolute path of the STRATEGO installation bin directory */
#define STRATEGO_BIN_PATH ""

/* Absolute path of the STRATEGO installation */
#define STRATEGO_INSTALL_PATH ""

/* Absolute path of the STRATEGO installation lib directory */
#define STRATEGO_LIBRARY_PATH ""

/* Controls design of internal template declaration support within the ROSE
   AST. */
#define TEMPLATE_DECLARATIONS_DERIVED_FROM_NON_TEMPLATE_DECLARATIONS /**/

/* Define to 1 if you can safely include both <sys/time.h> and <time.h>. */
#define TIME_WITH_SYS_TIME 1

/* Define to 1 if your <sys/time.h> declares `struct tm'. */
/* #undef TM_IN_SYS_TIME */

/* Mark that GFORTRAN is available */
#define USE_GFORTRAN_IN_ROSE 1

/* Link-time support for Insure. */
/* #undef USE_INSURE */

/* Support for Purify */
/* #undef USE_PURIFY */

/* Support for Purify API (Compiling with the Purify library). */
/* #undef USE_PURIFY_API */

/* Link-time support for Purify. */
/* #undef USE_PURIFY_LINKER */

/* Controls use of ROSE support for ATerm Library. */
/* #undef USE_ROSE_ATERM_SUPPORT */

/* Controls use of ROSE support for bddbddb (Binary decision diagrams (BDD)
   BDD-Based Deductive DataBase. */
/* #undef USE_ROSE_BDDBDDB_SUPPORT */

/* Controls use of BOOST WAVE support in ROSE. */
#define USE_ROSE_BOOST_WAVE_SUPPORT 1

/* Controls if EDG Union/Struct debugging support is to be used. */
#define USE_ROSE_EDG_DEBUGGING_SUPPORT 1

/* Use of GCC OpenMP in ROSE. */
/* #undef USE_ROSE_GCC_OMP */

/* Controls use of ROSE support for GLUT library. */
/* #undef USE_ROSE_GLUT_SUPPORT */

/* Controls use of ROSE support for GNAT ADA frontend Support. */
/* #undef USE_ROSE_GNAT_SUPPORT */

/* Controls use of ROSE support for GnuCOBOL parse-tree library. */
/* #undef USE_ROSE_GNU_COBOL_PT_SUPPORT */

/* Controls use of ROSE support for the modified GNU Octave parser. */
/* #undef USE_ROSE_GNU_OCTAVE_SUPPORT */

/* Controls use of ROSE support for OpenMP Translator targeting GCC 4.4 's
   GOMP OpenMP RTL. */
/* #undef USE_ROSE_GOMP_OPENMP_LIBRARY */

/* Controls use of IDA support for disassembling. */
/* #undef USE_ROSE_IDA_SUPPORT */

/* Controls use of ROSE support for Intel Pin Dynamic Instrumentation Package.
   */
/* #undef USE_ROSE_INTEL_PIN_SUPPORT */

/* Controls use of ROSE support for Java. */
#define USE_ROSE_INTERNAL_JAVA_SUPPORT /**/

/* Controls use of ROSE support for Java. */
#define USE_ROSE_JAVA_SUPPORT /**/

/* Controls use of ROSE support for LLVM. */
/* #undef USE_ROSE_LLVM_SUPPORT */

/* Controls use of ROSE support for Maple Symbolic Algebra Package. */
/* #undef USE_ROSE_MAPLE_SUPPORT */

/* Controls use of ROSE support for OpenMP Translator targeting Omni RTL. */
/* #undef USE_ROSE_OMNI_OPENMP_SUPPORT */

/* Controls use of ROSE support for PHP. */
/* #undef USE_ROSE_PHP_SUPPORT */

/* Controls use of ROSE support for Python. */
#define USE_ROSE_PYTHON_SUPPORT 1

/* Controls use of ROSE support for RTED library. */
/* #undef USE_ROSE_RTED_SUPPORT */

/* Controls use of ROSE support for internal Satisfiability (SAT) Solver. */
/* #undef USE_ROSE_SAT_SUPPORT */

/* Controls use of ROSE support for SSL (libssl -- MD5) library (incompatable
   with Java, so disables Fortran support). */
/* #undef USE_ROSE_SSL_SUPPORT */

/* Controls use of ROSE support for Stratego Library. */
/* #undef USE_ROSE_STRATEGO_SUPPORT */

/* Wine provides access to Windows header files for analysis of windows
   applications under Linux. */
/* #undef USE_ROSE_WINDOWS_ANALYSIS_SUPPORT */

/* Support for PURIFY debugging software. */
/* #undef USING_PURIFY */

/* Version number of package */
#define VERSION "0.9.10.54"

/* Define WORDS_BIGENDIAN to 1 if your processor stores words with the most
   significant byte first (like Motorola and SPARC, unlike Intel). */
#if defined AC_APPLE_UNIVERSAL_BUILD
# if defined __BIG_ENDIAN__
#  define WORDS_BIGENDIAN 1
# endif
#else
# ifndef WORDS_BIGENDIAN
/* #  undef WORDS_BIGENDIAN */
# endif
#endif

/* Absolute path of the X10 installation bin directory */
#define X10_BIN_PATH ""

/* Absolute path of the X10 installation */
#define X10_INSTALL_PATH ""

/* Absolute path of the X10 installation lib directory */
#define X10_LIBRARY_PATH ""

/* Version number of the user-specified X10 compiler */
#define X10_VERSION ""

/* Define to 1 if `lex' declares `yytext' as a `char *' by default, not a
   `char[]'. */
/* #undef YYTEXT_POINTER */

/* Define to 1 if type `char' is unsigned and you are not using gcc.  */
#ifndef __CHAR_UNSIGNED__
/* # undef __CHAR_UNSIGNED__ */
#endif

/* Define so that glibc/gnulib argp.h does not typedef error_t. */
/* #undef __error_t_defined */

/* Define to a type to use for `error_t' if it is not otherwise available. */
/* #undef error_t */

/* Define to `__inline__' or `__inline' if that's what the C compiler
   calls it, or to nothing if 'inline' is not supported under any name.  */
#ifndef __cplusplus
/* #undef inline */
#endif

/* Define to `long int' if <sys/types.h> does not define. */
/* #undef off_t */

/* Define to `unsigned int' if <sys/types.h> does not define. */
/* #undef size_t */

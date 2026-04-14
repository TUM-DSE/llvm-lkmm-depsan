cmake_minimum_required(VERSION 3.20)
project(PointerAssume)

# 1. Find the LLVM installation
find_package(LLVM REQUIRED CONFIG)

# 2. Add LLVM's include directories
include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})

# 3. Set the C++ standard (must match the LLVM you built)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 4. Disable RTTI if LLVM was built without it
if(NOT LLVM_ENABLE_RTTI)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

# 5. Create the shared library (your plugin)
add_library(PointerAssume SHARED pointer-assume.cpp)

# 6. Link against LLVM's libraries
target_link_libraries(PointerAssume ${LLVM_LIBRARY_DIRS})

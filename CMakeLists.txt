cmake_minimum_required(VERSION 3.22)

project(Project_Name VERSION 0.1.0 
  LANGUAGES ASM C CXX
  DESCRIPTION "A Project Template for writing verified C code"
)

# Testing options
option(ANVIL_BUILD_TESTS "Build the test suite" ON)
option(ANVIL_ENABLE_COVERAGE "Enable code coverage reporting" OFF)

# Sanitizer options
option(ANVIL_ENABLE_ASAN "Enable Address Sanitizer" OFF) # Cannot be combined with TSAN and MSAN
option(ANVIL_ENABLE_UBSAN "Enable Undefined Behavior Sanitizer" OFF)

# Memory checking options
option(ANVIL_ENABLE_VALGRIND "Enable Valgrind memory checking" OFF)

# Build type options
option(ANVIL_ENABLE_LTO "Enable Link Time Optimization" ON)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
include(CompilerStandards)
include(Functions)

# Configure sanitizers (set as variables for use in Functions.cmake)
if(ANVIL_ENABLE_ASAN)
  set(SANITIZER_FLAGS "${SANITIZER_FLAGS} -fsanitize=address -fno-omit-frame-pointer")
  set(SANITIZER_LINK_FLAGS "${SANITIZER_LINK_FLAGS} -fsanitize=address")
  message(STATUS "Address Sanitizer enabled")
endif()

if(ANVIL_ENABLE_UBSAN)
  set(SANITIZER_FLAGS "${SANITIZER_FLAGS} -fsanitize=undefined -fno-omit-frame-pointer")
  set(SANITIZER_LINK_FLAGS "${SANITIZER_LINK_FLAGS} -fsanitize=undefined")
  message(STATUS "Undefined Behavior Sanitizer enabled")
endif()

# Configure coverage
if(ANVIL_ENABLE_COVERAGE)
  set(COVERAGE_FLAGS "-O0 -g --coverage")
  set(COVERAGE_LINK_FLAGS "--coverage")
  message(STATUS "Code coverage enabled")
endif()

# Configure LTO/IPO
if(ANVIL_ENABLE_LTO)
  include(CheckIPOSupported)
  check_ipo_supported(RESULT ipo_supported OUTPUT ipo_error)
  if(ipo_supported)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
    message(STATUS "Link Time Optimization enabled")
  else()
    message(WARNING "LTO is not supported: ${ipo_error}")
  endif()
endif()

if(ANVIL_BUILD_TESTS)
    enable_testing()
    include(CTest)
    
    if (ANVIL_ENABLE_VALGRIND)
      find_program(VALGRIND_EXECUTABLE valgrind)
      if(VALGRIND_EXECUTABLE)
        set(MEMORYCHECK_COMMAND ${VALGRIND_EXECUTABLE})
        set(MEMORYCHECK_COMMAND_OPTIONS 
          "--leak-check=full"
          "--show-leak-kinds=definite,possible"
          "--track-origins=yes"
          "--error-exitcode=1")
        message(STATUS "Found Valgrind: ${VALGRIND_EXECUTABLE}")
      endif()
    endif()
endif()

# Creating an Example Executable - this would be replaced with your build instructions
add_executable(example src/main.c src/example.c src/multiply.cpp)
target_include_directories(example PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
set_compiler_options(example)

add_library(example_lib SHARED src/example.c src/multiply.cpp)
target_include_directories(example_lib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
set_compiler_options(example_lib)
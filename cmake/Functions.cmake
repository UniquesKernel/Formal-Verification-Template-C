function(set_compiler_options project_name)
  # Common flags for both C and C++
  set(COMMON_FLAGS
    -Wattributes
    -Wformat
    -Wformat-security
    -Werror=format-security
    -Wsign-conversion
    -Wcast-align
    -Wcast-qual
    -Wdouble-promotion 
    -Wfloat-equal
    -fno-strict-aliasing
    -Wundef
    -Wall
    -Wextra
    -Werror
    -Wpedantic
    -Wconversion
    -Wshadow
    -fno-plt
    -fPIC
  )

  # C-specific flags
  set(C_ONLY_FLAGS
    -Werror=implicit-function-declaration
    -Wstrict-prototypes 
    -Wmissing-prototypes 
    -Wold-style-definition
  )

  # Combine for the final compiler flags
  set(COMPILER_FLAGS ${COMMON_FLAGS})

  # Add optimization flags based on build type and coverage
  if(DEFINED COVERAGE_FLAGS)
    # Coverage mode: use -O0 for accurate coverage
    separate_arguments(COV_FLAGS UNIX_COMMAND "${COVERAGE_FLAGS}")
    list(APPEND COMPILER_FLAGS ${COV_FLAGS})
  elseif(CMAKE_BUILD_TYPE STREQUAL "Debug")
    list(APPEND COMPILER_FLAGS -O0 -g)
  elseif(CMAKE_BUILD_TYPE STREQUAL "RelWithDebInfo")
    list(APPEND COMPILER_FLAGS -O2 -g)
  else()
    # Release or default
    list(APPEND COMPILER_FLAGS -O3)
  endif()

  # Add sanitizer flags if enabled
  if(DEFINED SANITIZER_FLAGS)
    separate_arguments(SAN_FLAGS UNIX_COMMAND "${SANITIZER_FLAGS}")
    list(APPEND COMPILER_FLAGS ${SAN_FLAGS})
  endif()

  # Platform-specific flags
  if (UNIX)
    list(APPEND COMPILER_FLAGS -fPIE -pie)
  endif()

  if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    list(APPEND COMPILER_FLAGS -march=native)
    # Only add AVX2 if supported by march=native
    include(CheckCCompilerFlag)
    check_c_compiler_flag("-mavx2" COMPILER_SUPPORTS_AVX2)
    if(COMPILER_SUPPORTS_AVX2)
      list(APPEND COMPILER_FLAGS -mavx2)
    endif()
  endif()

  # Apply common flags to all languages
  target_compile_options(${project_name} PRIVATE ${COMPILER_FLAGS})
  
  # Apply C-specific flags only to C source files
  target_compile_options(${project_name} PRIVATE 
    $<$<COMPILE_LANGUAGE:C>:${C_ONLY_FLAGS}>
  )
  
  # Add linker flags for sanitizers and coverage
  if(DEFINED SANITIZER_LINK_FLAGS)
    separate_arguments(SAN_LINK_FLAGS UNIX_COMMAND "${SANITIZER_LINK_FLAGS}")
    target_link_options(${project_name} PRIVATE ${SAN_LINK_FLAGS})
  endif()
  
  if(DEFINED COVERAGE_LINK_FLAGS)
    separate_arguments(COV_LINK_FLAGS UNIX_COMMAND "${COVERAGE_LINK_FLAGS}")
    target_link_options(${project_name} PRIVATE ${COV_LINK_FLAGS})
  endif()
endfunction()

# Function to recursively find all source files
function(get_all_sources output_var root_dir)
    file(GLOB_RECURSE sources 
        "${root_dir}/*.c"
        "${root_dir}/*.s"
        "${root_dir}/*.asm"
    )
    set(${output_var} ${sources} PARENT_SCOPE)
endfunction()

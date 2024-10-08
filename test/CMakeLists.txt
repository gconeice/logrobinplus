#Testing macro
macro (add_test_executable_with_lib folder _name)
	add_executable(test_${folder}_${_name} "${folder}/${_name}.cpp")
	target_link_libraries(test_${folder}_${_name} ${EMP-OT_LIBRARIES} emp-zk)
endmacro()

macro (add_test_case folder _name)
	add_test_executable_with_lib(${folder} ${_name})
  	add_test(NAME ${folder}_${_name} COMMAND "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test_${folder}_${_name}" WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/")
endmacro()

macro (add_test_case_with_run folder _name)
	add_test_executable_with_lib(${folder} ${_name})
	add_test(NAME ${folder}_${_name} COMMAND "./run" "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test_${folder}_${_name}" WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/")

endmacro()

# Test Robin/Robin++/LogRobin/LogRobin++
# add_test_case_with_run(rand test)

add_test_case_with_run(rand arith_robin_it)
add_test_case_with_run(rand arith_robin_ro)

add_test_case_with_run(rand arith_logrobin_it)
add_test_case_with_run(rand arith_logrobin_ro)

add_test_case_with_run(rand arith_robinplus_it)
add_test_case_with_run(rand arith_robinplus_ro)

add_test_case_with_run(rand arith_logrobinplus_it)
add_test_case_with_run(rand arith_logrobinplus_ro)

add_test_case_with_run(rand bool_robin_it)
add_test_case_with_run(rand bool_robin_ro)

add_test_case_with_run(rand bool_logrobin_it)
add_test_case_with_run(rand bool_logrobin_ro)

add_test_case_with_run(rand bool_robinplus_it)
add_test_case_with_run(rand bool_robinplus_ro)

add_test_case_with_run(rand bool_logrobinplus_it)
add_test_case_with_run(rand bool_logrobinplus_ro)

# Test Robin/Robin++/LogRobin/LogRobin++
# With same circuit for each branch to save memory

add_test_case_with_run(rep arith_robin_it)
add_test_case_with_run(rep arith_robin_ro)

add_test_case_with_run(rep arith_logrobin_it)
add_test_case_with_run(rep arith_logrobin_ro)

add_test_case_with_run(rep arith_robinplus_it)
add_test_case_with_run(rep arith_robinplus_ro)

add_test_case_with_run(rep arith_logrobinplus_it)
add_test_case_with_run(rep arith_logrobinplus_ro)

add_test_case_with_run(rep bool_robin_it)
add_test_case_with_run(rep bool_robin_ro)

add_test_case_with_run(rep bool_logrobin_it)
add_test_case_with_run(rep bool_logrobin_ro)

add_test_case_with_run(rep bool_robinplus_it)
add_test_case_with_run(rep bool_robinplus_ro)

add_test_case_with_run(rep bool_logrobinplus_it)
add_test_case_with_run(rep bool_logrobinplus_ro)
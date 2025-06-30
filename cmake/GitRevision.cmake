function(git_rev_parse output_var source_dir)

    if (NOT DEFINED ${output_var})
        set(command git -C ${source_dir} rev-parse HEAD)

        execute_process(
            COMMAND ${command}
            OUTPUT_VARIABLE ${output_var}
            OUTPUT_STRIP_TRAILING_WHITESPACE
            RESULT_VARIABLE result
        )

        if (NOT result EQUAL 0)
            list(JOIN command " " command)
            message(WARNING "Command \"${command}\" failed; VCS information will be unavailable")
            set (${output_var} "UNKNOWN")
        endif()
    endif()

    message(STATUS "Got ${output_var}: ${${output_var}}")

    set(${output_var} ${${output_var}} PARENT_SCOPE)

endfunction()

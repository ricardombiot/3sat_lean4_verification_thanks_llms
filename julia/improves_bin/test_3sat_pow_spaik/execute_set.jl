function main(args)
    command_main = Cmd(["julia","./main.jl"])
    run(command_main)

    command_checker = Cmd(["julia","./checker.jl"])
    run(command_checker)
end

main(ARGS)

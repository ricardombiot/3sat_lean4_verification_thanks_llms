## Example:
# julia execute_new_set.jl n=5 l=8 c=30
function main(args)

    if isdir("./output")
        throw("please, save the previous output test before run it.")
    else
        mkdir("./output")
        base_path_instances = "./output/instances"
        base_path_solver_ex = "./output/solver_exhaustive"
        base_path_solver_machine = "./output/solver_sat_machine"

        mkdir(base_path_instances)
        mkdir(base_path_solver_ex)
        mkdir(base_path_solver_machine)
    end

    cd("./generators")
    command_generator = ["julia","./generator.jl"]
    for param in args
        push!(command_generator, "$(param)")
    end
    command_generator = Cmd(command_generator)
    run(command_generator)
    cd("./../")
    command_execute = Cmd(["julia","./execute_set.jl"])
    run(command_execute)
end

main(ARGS)

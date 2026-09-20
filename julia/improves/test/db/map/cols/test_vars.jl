function test_register_vars()
    col_vars = MapCollectionVars.new()

    MapCollectionVars.register_var!(col_vars, "x", Step(0))
    @test MapCollectionVars.get_step_var(col_vars, "x") == Step(0)
    @test MapCollectionVars.get_step_var(col_vars, "-x") == Step(1)
    @test MapCollectionVars.get_step_var(col_vars, "!x") == Step(1)

    @test MapCollectionVars.get_step_neg_var(col_vars, "x") == Step(1)
    @test MapCollectionVars.get_step_neg_var(col_vars, "!x") == Step(0)
    @test MapCollectionVars.get_step_neg_var(col_vars, "-x") == Step(0)
end

test_register_vars()

# Pruebas unitarias del mapa bin (docs/plans/bin-map.md, §4).
#
# Cubre: estructura/conteo, requires por literal, ventanas prohibidas, variables desplazadas,
# enlaces (sons/parents), construcción directa, y la semántica (mapa ↔ fórmula) de forma
# exhaustiva y sin máquina (chain_exists).

using Test

const PID = Alias.PathNodeId

# --- helpers para el test semántico ---------------------------------------

parse_lit(s) = (parse(Int, split(s, "=")[1]), parse(Int, split(s, "=")[2]))

# title "v=b" (literal positivo) o "!v=b" (negativo); devuelve si la asignación cumple ese literal.
function literal_consistent(title :: String, asig :: BitArray) :: Bool
    if startswith(title, "!")
        v, b = parse_lit(title[2:end])
        return (asig[v] ? 1 : 0) == (1 - b)
    else
        v, b = parse_lit(title)
        return (asig[v] ? 1 : 0) == b
    end
end

function node_consistent(gmap, node, asig) :: Bool
    for rid in node.requires
        rnode = GraphMapBin.get_node(gmap, rid)
        rnode === nothing && return false
        literal_consistent(rnode.title, asig) || return false
    end
    return true
end

# Recorre el DAG por capas (sons + requires + ventana prohibida), como el UP de la máquina,
# y devuelve si existe una cadena consistente con la asignación.
function chain_exists(gmap, asig) :: Bool
    reachable = Set{PID}([Alias.root_path_id((step = 0, index = 0))])
    for s in 1:gmap.step - 1
        next = Set{PID}()
        for last in reachable
            pnode = GraphMapBin.get_node(gmap, last.id)
            for sid in pnode.sons
                new_pid = Alias.shift_path_id(last, sid)
                new_pid in gmap.prohibited_windows && continue
                snode = GraphMapBin.get_node(gmap, sid)
                node_consistent(gmap, snode, asig) || continue
                push!(next, new_pid)
            end
        end
        reachable = next
        isempty(reachable) && return false
    end
    return !isempty(reachable)
end

n_vars_of(path) = begin
    for line in eachline(path)
        if startswith(line, "p")
            return parse(Int, split(line, " ")[3])
        end
    end
    -1
end

# --- fichero de prueba ----------------------------------------------------

const BIN_CNF = joinpath(@__DIR__, "../example_cnf/bin_v3_c2.cnf")

@testset "estructura y conteo" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)   # n=3, m=2 -> stepCount = 2*3+3*2+3 = 15
    @test g.step == 15

    @test length(GraphMapBin.get_ids_step(g, 0)) == 1   # fusión raíz
    for v in 1:3
        @test length(GraphMapBin.get_ids_step(g, 2v - 1)) == 2
        @test length(GraphMapBin.get_ids_step(g, 2v)) == 2
    end
    @test length(GraphMapBin.get_ids_step(g, 7)) == 1    # fusión media (2n+1)
    for j in 0:1
        @test length(GraphMapBin.get_ids_step(g, 8 + 3j)) == 2   # L1_j
        @test length(GraphMapBin.get_ids_step(g, 9 + 3j)) == 2   # L2_j
        @test length(GraphMapBin.get_ids_step(g, 10 + 3j)) == 2  # L3_j
    end
    @test length(GraphMapBin.get_ids_step(g, 14)) == 1   # fusión final (2n+3m+2)

    @test GraphMapBin.get_node(g, (step = 0, index = 0)).title == "FusionNode"
    @test GraphMapBin.get_node(g, (step = 7, index = 0)).title == "FusionNode"
    @test GraphMapBin.get_node(g, (step = 14, index = 0)).title == "FusionNode"
end

@testset "requires por literal" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)
    # cláusula 0 = "1 2 3": l1=1 (paso 1), l2=2 (paso 3), l3=3 (paso 5)
    @test Set(GraphMapBin.get_node(g, (step = 8, index = 0)).requires) == Set([(step = 1, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 8, index = 1)).requires) == Set([(step = 1, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 9, index = 0)).requires) == Set([(step = 3, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 9, index = 1)).requires) == Set([(step = 3, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 10, index = 0)).requires) == Set([(step = 5, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 10, index = 1)).requires) == Set([(step = 5, index = 1)])
    # cláusula 1 = "-1 2 -3": l1=-1 (paso 2), l2=2 (paso 3), l3=-3 (paso 6)
    @test Set(GraphMapBin.get_node(g, (step = 11, index = 0)).requires) == Set([(step = 2, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 11, index = 1)).requires) == Set([(step = 2, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 12, index = 0)).requires) == Set([(step = 3, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 12, index = 1)).requires) == Set([(step = 3, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 13, index = 0)).requires) == Set([(step = 6, index = 0)])
    @test Set(GraphMapBin.get_node(g, (step = 13, index = 1)).requires) == Set([(step = 6, index = 1)])
end

@testset "ventanas prohibidas" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)
    @test length(g.prohibited_windows) == 2
    @test PID((step = 8, index = 0), (step = 9, index = 0), (step = 10, index = 0)) in g.prohibited_windows
    @test PID((step = 11, index = 0), (step = 12, index = 0), (step = 13, index = 0)) in g.prohibited_windows
end

@testset "variables desplazadas" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)
    @test Set(GraphMapBin.get_ids_step(g, 1)) == Set([(step = 1, index = 0), (step = 1, index = 1)])
    @test Set(GraphMapBin.get_ids_step(g, 6)) == Set([(step = 6, index = 0), (step = 6, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 2, index = 0)).requires) == Set([(step = 1, index = 1)])
    @test Set(GraphMapBin.get_node(g, (step = 2, index = 1)).requires) == Set([(step = 1, index = 0)])
end

@testset "enlaces" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)
    root = GraphMapBin.get_node(g, (step = 0, index = 0))
    @test Set(root.sons) == Set([(step = 1, index = 0), (step = 1, index = 1)])
    mid = GraphMapBin.get_node(g, (step = 7, index = 0))
    @test Set(mid.parents) == Set([(step = 6, index = 0), (step = 6, index = 1)])
    @test Set(mid.sons) == Set([(step = 8, index = 0), (step = 8, index = 1)])
    l2 = GraphMapBin.get_node(g, (step = 9, index = 0))
    @test Set(l2.sons) == Set([(step = 10, index = 0), (step = 10, index = 1)])
end

@testset "construcción directa" begin
    g = GraphMapBin.new()
    @test g.step == 1   # el fusión raíz ya está creado
    GraphMapBin.add_var!(g, "1")
    GraphMapBin.add_var!(g, "2")
    GraphMapBin.add_var!(g, "3")
    GraphMapBin.close_vars!(g)
    GraphMapBin.add_gate_bin!(g, "1", "2", "3")
    GraphMapBin.close_gates!(g)
    @test g.step == 2 * 3 + 3 * 1 + 3   # 12
    @test length(g.prohibited_windows) == 1
end

@testset "semántica (mapa ↔ fórmula)" begin
    g = GraphMapBin.load_import_bin!(BIN_CNF)
    n = n_vars_of(BIN_CNF)
    @test n == 3
    for mask in 0:(2^n - 1)
        asig = BitArray(undef, n)
        for v in 1:n
            asig[v] = ((mask >> (v - 1)) & 1) == 1
        end
        @test chain_exists(g, asig) == CheckerCnf.test(asig, BIN_CNF)
    end
end

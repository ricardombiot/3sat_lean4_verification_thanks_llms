# ¿Las piezas (UP con filtro, sin review) y los estados unidos cumplen el contexto de kernel?
# (lean/improves_bin, Kernel.Kernel + SelfOwn.OOS; GrowCert.growR_iff_mapCert lo pide)
# Campos: gow, gn, own, valid, sym, linkP, linkS, pair, nbrP, nbrS, oos. Cuenta estados que fallan cada uno.
#   julia --project=../.. kernel_probe.jl f1.cnf ...
include("./../../src/main.jl")
get(ENV, "LINK", "off") == "on" && (GraphPath.LINK_MODE[] = :on)
function nodes(g)
    D = Dict{PathNodeId, Any}()
    for (_, line) in g.table_lines.table, (pid, node) in line.table; D[pid] = node; end
    D
end
tab(n) = (S = Set{PathNodeId}(); for (_, set) in n.owners.table; union!(S, set); end; S)
function gown(g)
    S = Set{PathNodeId}(); for (_, set) in g.owners.table; union!(S, set); end; S
end
function check!(st, tag, g)
    g.is_valid || return
    D = nodes(g); isempty(D) && return
    T = Dict(r => tab(n) for (r, n) in D); G = gown(g)
    top = maximum(p.id.step for p in keys(D))
    fails = Set{String}()
    f(k) = push!(fails, k)
    for (p, n) in D
        p in G || f("gow")
        for v in T[p]
            v in G || f("own")
            haskey(D, v) && !(p in T[v]) && f("sym")
            v.id.step == p.id.step && v != p && f("oos")
            if p.id.step >= 1 && !any(c -> haskey(D, c) && v in T[c], n.parents); f("nbrP"); end
            if p.id.step <= top - 1 && !any(c -> haskey(D, c) && v in T[c], n.sons); f("nbrS"); end
            if haskey(D, v)
                for k in 0:top
                    any(r -> r.id.step == k && r in T[v], T[p]) || (f("pair"); break)
                end
            end
        end
        all(k -> any(v -> v.id.step == k, T[p]), 0:top) || f("valid: paso sin entrada")
        p.id.step >= 1 && isempty(n.parents) && f("valid: sin padre")
        p.id.step < top && isempty(n.sons) && f("valid: sin hijo")
        for (nm, cs) in (("linkP", n.parents), ("linkS", n.sons)), c in cs
            haskey(D, c) || (f("$nm: enlace a nodo ausente"); continue)
            c in T[p] || f("$nm: enlace a no-poseído")
            if !(c in T[p]) && nm == "linkP"
                f("  linkP caducado: p paso=top-$(top - p.id.step)")
            end
            p in T[c] || f("$nm: el otro no me posee")
            (c.id.step == p.id.step + (nm == "linkS" ? 1 : -1)) || f("$nm: paso")
        end
    end
    for q in G; haskey(D, q) || f("gn"); end
    if !isempty(fails) && get(st, "ej", 0) < 3
        st["ej"] = get(st, "ej", 0) + 1
        for (p, n) in D, c in n.parents
            haskey(D, c) && continue
            println("  ej $tag top=$top p=$(p.id) parent_id=$(p.parent_id) enlace ausente=$(c.id)/$(c.parent_id)"); break
        end
    end
    st["$tag estados"] = get(st, "$tag estados", 0) + 1
    isempty(fails) && (st["$tag kernel ok"] = get(st, "$tag kernel ok", 0) + 1)
    for k in fails; st["$tag FALLA $k"] = get(st, "$tag FALLA $k", 0) + 1; end
end
function probe(path, st)
    gmap = GraphMapBin.load_import_bin!(path)
    m = SatMachine.new(gmap); SatMachine.init!(m)
    while !(SatMachine.is_finished(m) || !SatMachine.have_gpaths_step(m))
        s = m.current_step
        CollectionTimeline.for_each_gpath(m.timeline, s, function (g)
            check!(st, "línea", g)
            node = SatMachine.map_get_node(gmap, g.map_parent_id)
            for d in node.sons
                dn = SatMachine.map_get_node(gmap, d)
                fl = deepcopy(g)
                redirect_stdout(devnull) do; GraphPath.filter!(fl, dn.requires); end
                check!(st, "filtro (sin UP)", fl)
                fl2 = deepcopy(g); fl2.review_owners = true
                redirect_stdout(devnull) do; GraphPath.filter!(fl2, dn.requires); end
                check!(st, "filtro con review forzada", fl2)
                p = deepcopy(g)
                redirect_stdout(devnull) do
                    GraphPath.do_up_filtering!(p, dn.requires, d, dn.title, SatMachine.map_prohibited(gmap))
                end
                check!(st, "pieza", p)
            end
        end)
        redirect_stdout(devnull) do; SatMachine.make_step!(m); end
    end
end
st = Dict{String, Int}()
for f in ARGS
    try probe(f, st) catch err; println("$(basename(f)): SALTADA ($err)"); end
end
for (k, v) in sort(collect(st)); println("  $k: $v"); end

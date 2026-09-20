Bien, ahora veo la estructura. Aquí está cómo se verían **en la máquina Julia original**:

## `symmetric_entry` — Verifica simetría de owners

```julia
function symmetric_entry(gpath :: GPath, path_node_x :: PathDocNode, 
                         path_node_w :: PathDocNode) :: Bool
    # ¿Está w en los owners de x Y está x en los owners de w?
    x_owns_w = PathDocumentOwners.is_owner(path_node_x.owners, path_node_w.id)
    w_owns_x = PathDocumentOwners.is_owner(path_node_w.owners, path_node_x.id)
    
    return x_owns_w && w_owns_x
end
```

## `pair_support_exists` — Verifica si comparten owner vivo en algún paso

```julia
function pair_support_exists(gpath :: GPath, path_node_x :: PathDocNode, 
                            path_node_w :: PathDocNode) :: Bool
    # ¿Existe un paso k' con owner vivo q que posee ambos x y w?
    x_step = PathDocumentNode.get_step(path_node_x)
    w_step = PathDocumentNode.get_step(path_node_w)
    
    # Iterar sobre todos los pasos (menos el de x y el de w)
    for step in 0:gpath.current_step-1
        if step == x_step || step == w_step
            continue
        end
        
        # Sacar owners de este paso
        owners_at_step = PathDocumentOwners.get(gpath.owners, step)
        if owners_at_step == nothing
            continue
        end
        
        # Chequear si algún dueño vivo q en este paso posee ambos x y w
        for owner_id in owners_at_step
            # Traer el nodo dueño
            owner_node = PathCollectionLines.get_node(gpath.table_lines, owner_id)
            
            # ¿Posee el dueño a ambos?
            owns_x = PathDocumentOwners.is_owner(owner_node.owners, path_node_x.id)
            owns_w = PathDocumentOwners.is_owner(owner_node.owners, path_node_w.id)
            
            if owns_x && owns_w
                return true  # Encontró soporte por parejas
            end
        end
    end
    
    return false  # No encontró soporte
end
```

## Integración en el `review` de v100

```julia
function review_with_stale_cleanup!(gpath :: GPath)
    # Paso 1: review estándar
    make_review_owners!(gpath)
    
    # Paso 2: iterar limpiar owners obsoletos hasta punto fijo
    repeat do
        prev_valid_count = count_valid_entries(gpath)
        
        # Para cada nodo en cada paso
        for step in 0:gpath.current_step-1
            col_nodes = PathCollectionLines.get_step(gpath.table_lines, step)
            
            PathCollectionNodes.filter!(col_nodes, function (path_node_x)
                if !PathDocumentNode.is_valid(path_node_x)
                    return false  # Ya inválido, saltar
                end
                
                # Copiar porque vamos a filtrar dentro del loop
                owners_copy = deepcopy(
                    PathDocumentOwners.get(path_node_x.owners, step)
                )
                
                for owner_id in owners_copy
                    owner_node = PathCollectionLines.get_node(
                        gpath.table_lines, owner_id
                    )
                    
                    # Aplicar 3 criterios de la regla
                    if is_node(owner_node) &&
                       (symmetric_entry(gpath, path_node_x, owner_node) ||
                        pair_support_exists(gpath, path_node_x, owner_node))
                        # Mantener esta entrada
                        continue
                    else
                        # Quitar entrada obsoleta
                        PathDocumentOwners.remove!(path_node_x.owners, owner_id)
                    end
                end
                
                return !PathDocumentNode.is_valid(path_node_x)
            end)
        end
        
        curr_valid_count = count_valid_entries(gpath)
    until curr_valid_count == prev_valid_count
end
```

**Clave de la estructura original:** 
- Los owners viven en dos lugares: global (`gpath.owners` = tabla por pasos) y local (`path_node.owners` = tabla por paso de cada nodo)
- El review original (líneas 80-117 de `graph_path_filter.jl`) usa unión e intersección de esas tablas
- La regla de v100 añadiría un paso extra que **quita entradas específicas** sin tocar toda la tabla, cosa que la máquina original no hacía
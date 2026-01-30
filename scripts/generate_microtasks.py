#!/usr/bin/env python3
"""
Script para generar microtareas a partir del inventario de funciones Julia.
Lee el archivo 'julia_functions_inventory.csv' y crea archivos de microtareas
en 'tasks/work/' siguiendo la plantilla.
También actualiza los archivos de fase con la lista de IDs de microtareas.
"""

import csv
import os
from pathlib import Path

# Mapeo de archivos a fases (basado en el diseño revisado)
PHASE_MAP = {
    # P1
    "utils/alias.jl": "P1",
    "db/path/docs/path_doc_node.jl": "P1",
    "db/map/docs/map_doc_node.jl": "P1",
    # P2
    "db/map/cols/map_col_vars.jl": "P2",
    "db/map/cols/map_col_nodes.jl": "P2",
    "db/map/cols/map_col_lines.jl": "P2",
    # P3
    "graph_map/graph_map.jl": "P3",
    "graph_map/graph_map_import_cnf.jl": "P3",
    "graph_map/graph_map_visual.jl": "P3",
    # P4
    "db/path/cols/path_col_lines.jl": "P4",
    "db/path/cols/path_col_nodes.jl": "P4",
    "graph_path/graph_path.jl": "P4",  # solo parte básica, pero lo trataremos completo
    # P5
    "graph_path/graph_path_constructor.jl": "P5",
    "graph_path/graph_path_filter.jl": "P5",
    "graph_path/graph_path_join.jl": "P5",
    "graph_path/graph_path_up.jl": "P5",
    "graph_path/graph_path_visual.jl": "P5",
    "graph_path/reader/path_reader.jl": "P5",
    "graph_path/reader/path_exp_reader.jl": "P5",
    # P6
    "graph_pow/graph_pow.jl": "P6",
    "graph_pow/graph_pow_abstract_node.jl": "P6",
    "graph_pow/graph_pow_filter.jl": "P6",
    "graph_pow/graph_pow_join.jl": "P6",
    "graph_pow/graph_pow_up.jl": "P6",
    "graph_pow/graph_pow_visual.jl": "P6",
    "graph_pow/reader/path_pow_reader.jl": "P6",
    "graph_pow/reader/path_pow_exp_reader.jl": "P6",
    "db/machine/cols/col_timeline_step.jl": "P6",
    "db/machine/cols/col_timeline_pow_step.jl": "P6",
    "db/machine/cols/col_timeline.jl": "P6",
    "db/machine/cols/col_timeline_pow.jl": "P6",
    # P7
    "sat_machine/sat_machine.jl": "P7",
    "sat_machine/sat_machine_pow.jl": "P7",
    "utils/checker.jl": "P7",
    "utils/exaustive_solver.jl": "P7",
}

def load_inventory(csv_path):
    """Carga el inventario desde el CSV."""
    inventory = []
    with open(csv_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            inventory.append(row)
    return inventory

def group_by_file_and_phase(inventory):
    """Agrupa funciones por archivo y fase."""
    groups = {}
    for item in inventory:
        file = item['file']
        phase = PHASE_MAP.get(file)
        if phase is None:
            # Si no está en el mapa, asignar a P7 (por defecto) o ignorar
            phase = "P7"
        key = (phase, file)
        if key not in groups:
            groups[key] = []
        groups[key].append(item)
    return groups

def chunk_functions(func_list, chunk_size=2):
    """Divide la lista de funciones en chunks de tamaño chunk_size."""
    for i in range(0, len(func_list), chunk_size):
        yield func_list[i:i + chunk_size]

def create_microtask(task_id, phase, file, functions, output_dir):
    """Crea un archivo de microtarea."""
    task_path = output_dir / f"task_{task_id:04d}.md"
    
    # Preparar descripción de funciones
    func_desc = "\n".join([f"- `{f['function']}` (línea {f['line']})" for f in functions])
    func_names = ", ".join([f['function'] for f in functions])
    
    # Determinar dependencias basadas en fase
    dependencies = []
    if phase == "P1":
        dependencies = ["Ninguna"]
    elif phase == "P2":
        dependencies = ["P1"]
    elif phase == "P3":
        dependencies = ["P2"]
    elif phase == "P4":
        dependencies = ["P1"]
    elif phase == "P5":
        dependencies = ["P4"]
    elif phase == "P6":
        dependencies = ["P3", "P5"]
    elif phase == "P7":
        dependencies = ["P3", "P5", "P6"]
    
    # Convertir dependencias a string
    if isinstance(dependencies, list):
        deps_str = ", ".join(dependencies) if dependencies else "Ninguna"
    else:
        deps_str = dependencies
    
    # Leer la plantilla de microtarea
    template_path = Path("tasks/templates/task.md")
    with open(template_path, 'r', encoding='utf-8') as f:
        template = f.read()
    
    # Reemplazar campos en la plantilla
    content = template.replace("[Identificador único de 4 dígitos, ej. 0042]", f"{task_id:04d}")
    content = content.replace("[Rol responsable: Developer, QA, DevOps, Project Manager, Architect, etc.]", "Developer")
    content = content.replace("[Identificador de la fase a la que pertenece la microtarea, ej. P1, P2, etc.]", phase)
    
    # Prioridad: Alta si es P1 o P2, Media si es P3 o P4, Baja para el resto
    if phase in ["P1", "P2"]:
        priority = "Alta"
    elif phase in ["P3", "P4"]:
        priority = "Media"
    else:
        priority = "Baja"
    content = content.replace("[Alta/Media/Baja - basada en dependencias y valor]", priority)
    
    # Dependencias
    content = content.replace("[Lista de TASK IDs que deben completarse antes, ej. 0040, 0041. Si no hay, escribir \"Ninguna\".]", deps_str)
    
    # SHOULD TARGET
    target = f"Migrar y verificar las funciones {func_names} del archivo `{file}` a Lean 4."
    content = content.replace("[Descripción clara del objetivo o resultado esperado de la tarea, especificando qué se espera lograr con esta microtarea y cómo contribuirá al avance general del proyecto. El objetivo debe ser medible y alineado con los objetivos generales del proyecto.]", target)
    
    # SHOULD DO
    should_do = f"""1. Analizar el código Julia de las funciones:
{func_desc}
2. Diseñar la representación en Lean 4, respetando los tipos y semántica.
3. Implementar las funciones en el módulo Lean correspondiente (según la estructura del proyecto).
4. Escribir teoremas que verifiquen propiedades clave de las funciones (correctitud, invariantes, etc.).
5. Probar la implementación con ejemplos concretos y asegurar que compila."""
    content = content.replace("[Descripción detallada de la acción o trabajo que debe realizarse, incluyendo los pasos específicos, metodologías o herramientas que se deben utilizar para completar la tarea de manera efectiva. Incluye criterios de aceptación y posibles dependencias con otras tareas para facilitar la ejecución.]", should_do)
    
    # ACCEPTANCE CRITERIA
    acceptance = f"""1. Las funciones {func_names} están implementadas en Lean 4 y su comportamiento coincide con el de Julia.
2. Se han escrito al menos dos teoremas por función que demuestran propiedades relevantes.
3. El código compila sin errores en el proyecto `docs/lean/abs_sat/`.
4. Se incluyen ejemplos de uso en forma de `#eval` o `example`."""
    content = content.replace("[Criterio verificable 1]\n2. [Criterio verificable 2]\n3. [Criterio verificable 3]", acceptance)
    
    # RESOURCES
    resources = f"- `docs/original_julia/src/{file}`\n- `docs/project_main.md`\n- `docs/lean/abs_sat/` (proyecto Lean)"
    content = content.replace("[Enlaces a `project_main.md`, `/docs`, diseños, APIs, o cualquier recurso relevante.]", resources)
    
    # POTENTIAL RISKS
    risks = f"""- Las funciones pueden tener dependencias de otros módulos no migrados aún.
- La semántica de Julia puede no traducirse directamente a Lean (manejo de mutabilidad, errores).
- La verificación formal puede requerir lemas auxiliares no triviales."""
    content = content.replace("[Posibles bloqueos, dificultades anticipadas, y alternativas si se presentan.]", risks)
    
    # SCOPE
    scope = f"""Esta microtarea cubre exclusivamente la migración y verificación de las funciones {func_names} del archivo `{file}`.
Quedan excluidas modificaciones a otros archivos Lean, optimizaciones de rendimiento y la implementación de funcionalidades adicionales no presentes en el código Julia original."""
    content = content.replace("[Definir el alcance de la tarea, indicando claramente qué partes del proyecto están incluidas dentro de esta microtarea y cuáles quedan excluidas. Delimitar límites temporales, funcionales o técnicos, así como cualquier restricción o requisito especial.]", scope)
    
    # Escribir archivo
    with open(task_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    return task_id, phase, file, [f['function'] for f in functions]

def update_phase_file(phase_id, task_ids, phase_dir):
    """Actualiza el archivo de fase con la lista de MICROTASKS."""
    phase_path = phase_dir / f"phase_{phase_id}.md"
    if not phase_path.exists():
        print(f"Advertencia: archivo de fase {phase_path} no existe.")
        return
    
    with open(phase_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Buscar la línea MICROTASKS y reemplazar
    lines = content.split('\n')
    in_microtasks = False
    new_lines = []
    for line in lines:
        if line.strip() == "**MICROTASKS:**":
            new_lines.append(line)
            new_lines.append("[Se actualizará conforme se creen las microtareas]")
            in_microtasks = True
        elif in_microtasks and line.strip().startswith("**"):
            # Terminó la sección MICROTASKS
            in_microtasks = False
            new_lines.append(line)
        elif not in_microtasks:
            new_lines.append(line)
    
    # Reemplazar con la lista real
    updated_content = "\n".join(new_lines)
    task_list = ", ".join([f"{tid:04d}" for tid in task_ids])
    updated_content = updated_content.replace(
        "[Se actualizará conforme se creen las microtareas]",
        task_list
    )
    
    with open(phase_path, 'w', encoding='utf-8') as f:
        f.write(updated_content)

def main():
    csv_path = Path("julia_functions_inventory.csv")
    if not csv_path.exists():
        print("Error: No se encuentra 'julia_functions_inventory.csv'. Ejecuta primero inventory_julia_functions.py.")
        return
    
    inventory = load_inventory(csv_path)
    print(f"Inventario cargado: {len(inventory)} funciones.")
    
    groups = group_by_file_and_phase(inventory)
    print(f"Archivos agrupados: {len(groups)} grupos (fase, archivo).")
    
    # Crear directorio de microtareas
    work_dir = Path("tasks/work")
    work_dir.mkdir(exist_ok=True)
    
    # Generar microtareas
    task_id = 2  # empezar desde 0002 (TASK ID 0001 es el director)
    phase_tasks = {}  # fase -> lista de task_ids
    
    for (phase, file), funcs in sorted(groups.items()):
        print(f"Procesando {file} (fase {phase}) con {len(funcs)} funciones...")
        # Dividir en chunks de 2-3 funciones
        chunks = list(chunk_functions(funcs, chunk_size=2))
        for chunk in chunks:
            tid, p, f, names = create_microtask(task_id, phase, file, chunk, work_dir)
            if p not in phase_tasks:
                phase_tasks[p] = []
            phase_tasks[p].append(tid)
            print(f"  Creada tarea {tid:04d} para funciones: {', '.join(names)}")
            task_id += 1
    
    # Actualizar archivos de fase
    phase_dir = Path("tasks/phases")
    for phase, ids in phase_tasks.items():
        update_phase_file(phase, ids, phase_dir)
        print(f"Fase {phase} actualizada con {len(ids)} microtareas.")
    
    print(f"\nTotal de microtareas generadas: {task_id - 2}")
    print(f"Archivos guardados en {work_dir}/")
    
    # Crear un resumen
    summary_path = Path("tasks/microtasks_summary.md")
    with open(summary_path, 'w', encoding='utf-8') as f:
        f.write("# Resumen de Microtareas Generadas\n\n")
        f.write(f"Total: {task_id - 2} microtareas\n\n")
        for phase in sorted(phase_tasks.keys()):
            f.write(f"## Fase {phase}\n")
            f.write(f"Microtareas: {', '.join([f'{tid:04d}' for tid in phase_tasks[phase]])}\n")
            f.write(f"Cantidad: {len(phase_tasks[phase])}\n\n")
    
    print(f"Resumen guardado en {summary_path}")

if __name__ == '__main__':
    main()

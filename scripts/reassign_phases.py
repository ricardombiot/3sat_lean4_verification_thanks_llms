#!/usr/bin/env python3
"""
Script para reasignar fases a microtareas ya generadas, basándose en un mapeo actualizado.
Lee los archivos task_XXXX.md en tasks/work/, actualiza el campo PHASE y luego actualiza
los archivos de fase en tasks/phases/ con las listas correctas.
"""

import csv
import re
from pathlib import Path

# Mapeo actualizado de archivos a fases (basado en diseño revisado)
PHASE_MAP_UPDATED = {
    # P1: Tipos fundamentales
    "utils/alias.jl": "P1",
    "db/path/docs/path_doc_node.jl": "P1",
    "db/path/docs/path_doc_owners.jl": "P1",
    "db/map/docs/map_doc_node.jl": "P1",
    # P2: Colecciones de mapas
    "db/map/cols/map_col_vars.jl": "P2",
    "db/map/cols/map_col_nodes.jl": "P2",
    "db/map/cols/map_col_lines.jl": "P2",
    # P3: GraphMap
    "graph_map/graph_map.jl": "P3",
    "graph_map/graph_map_import_cnf.jl": "P3",
    "graph_map/graph_map_visual.jl": "P3",
    # P4: Colecciones de paths y GraphPath base
    "db/path/cols/path_col_lines.jl": "P4",
    "db/path/cols/path_col_nodes.jl": "P4",
    "graph_path/graph_path.jl": "P4",
    # P5: GraphPath avanzado y lectores
    "graph_path/graph_path_constructor.jl": "P5",
    "graph_path/graph_path_filter.jl": "P5",
    "graph_path/graph_path_join.jl": "P5",
    "graph_path/graph_path_up.jl": "P5",
    "graph_path/graph_path_visual.jl": "P5",
    "graph_path/reader/path_reader.jl": "P5",
    "graph_path/reader/path_exp_reader.jl": "P5",
    # P6: GraphPow y colecciones de máquina
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
    # P7: SatMachine y verificaciones
    "sat_machine/sat_machine.jl": "P7",
    "sat_machine/sat_machine_pow.jl": "P7",
    "utils/checker.jl": "P7",
    "utils/exaustive_solver.jl": "P7",
}

def extract_file_from_task(task_path):
    """Extrae el nombre del archivo Julia de la microtarea (del campo SHOULD TARGET)."""
    with open(task_path, 'r', encoding='utf-8') as f:
        content = f.read()
    # Buscar línea que contenga "del archivo `...`"
    match = re.search(r'del archivo `([^`]+)`', content)
    if match:
        return match.group(1)
    # Alternativa: buscar en SHOULD TARGET
    lines = content.split('\n')
    for line in lines:
        if 'SHOULD TARGET' in line or 'Migrar y verificar' in line:
            match = re.search(r'`([^`]+)`', line)
            if match:
                return match.group(1)
    return None

def update_phase_in_task(task_path, new_phase):
    """Actualiza el campo PHASE en el archivo de microtarea."""
    with open(task_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    updated = False
    for i, line in enumerate(lines):
        if line.strip().startswith('**PHASE:**'):
            # Reemplazar la línea entera
            lines[i] = f"**PHASE:** {new_phase}\n"
            updated = True
            break
    
    if updated:
        with open(task_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)
        return True
    return False

def update_priority_based_on_phase(task_path, phase):
    """Actualiza la prioridad según la fase."""
    priority_map = {
        "P1": "Alta",
        "P2": "Alta",
        "P3": "Media",
        "P4": "Media",
        "P5": "Media",
        "P6": "Baja",
        "P7": "Baja",
    }
    new_priority = priority_map.get(phase, "Media")
    
    with open(task_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    updated = False
    for i, line in enumerate(lines):
        if line.strip().startswith('**PRIORITY:**'):
            lines[i] = f"**PRIORITY:** {new_priority}\n"
            updated = True
            break
    
    if updated:
        with open(task_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)

def update_dependencies_based_on_phase(task_path, phase):
    """Actualiza las dependencias según la fase."""
    dep_map = {
        "P1": "Ninguna",
        "P2": "P1",
        "P3": "P2",
        "P4": "P1",
        "P5": "P4",
        "P6": "P3, P5",
        "P7": "P3, P5, P6",
    }
    new_deps = dep_map.get(phase, "Ninguna")
    
    with open(task_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    updated = False
    for i, line in enumerate(lines):
        if line.strip().startswith('**DEPENDENCIES:**'):
            lines[i] = f"**DEPENDENCIES:** {new_deps}\n"
            updated = True
            break
    
    if updated:
        with open(task_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)

def collect_tasks(work_dir):
    """Recorre tasks/work/ y devuelve lista de (task_id, task_path, julia_file)."""
    tasks = []
    for task_file in work_dir.glob("task_*.md"):
        match = re.search(r'task_(\d{4})\.md', task_file.name)
        if match:
            task_id = int(match.group(1))
            julia_file = extract_file_from_task(task_file)
            tasks.append((task_id, task_file, julia_file))
    return sorted(tasks, key=lambda x: x[0])

def update_phase_files(phase_tasks, phase_dir):
    """Actualiza los archivos de fase con la lista de microtareas."""
    for phase, task_ids in phase_tasks.items():
        phase_path = phase_dir / f"phase_{phase}.md"
        if not phase_path.exists():
            print(f"Advertencia: archivo de fase {phase_path} no existe.")
            continue
        
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
        task_list = ", ".join([f"{tid:04d}" for tid in sorted(task_ids)])
        updated_content = updated_content.replace(
            "[Se actualizará conforme se creen las microtareas]",
            task_list
        )
        
        with open(phase_path, 'w', encoding='utf-8') as f:
            f.write(updated_content)
        print(f"Fase {phase} actualizada con {len(task_ids)} microtareas: {task_list}")

def main():
    work_dir = Path("tasks/work")
    phase_dir = Path("tasks/phases")
    
    if not work_dir.exists():
        print("Error: No se encuentra tasks/work/")
        return
    
    tasks = collect_tasks(work_dir)
    print(f"Encontradas {len(tasks)} microtareas.")
    
    phase_tasks = {}  # fase -> lista de task_ids
    for task_id, task_path, julia_file in tasks:
        if julia_file is None:
            print(f"Advertencia: No se pudo extraer archivo Julia de {task_path.name}")
            continue
        
        # Determinar fase
        phase = None
        for pattern, ph in PHASE_MAP_UPDATED.items():
            if pattern in julia_file:
                phase = ph
                break
        
        if phase is None:
            # Si no coincide, usar la fase actual del archivo (leer del contenido)
            with open(task_path, 'r', encoding='utf-8') as f:
                content = f.read()
                match = re.search(r'\*\*PHASE:\*\*\s*(\w+)', content)
                if match:
                    phase = match.group(1)
                else:
                    phase = "P7"  # default
            print(f"Advertencia: Archivo {julia_file} no está en PHASE_MAP. Usando fase {phase}.")
        
        # Actualizar campos en la microtarea
        if update_phase_in_task(task_path, phase):
            update_priority_based_on_phase(task_path, phase)
            update_dependencies_based_on_phase(task_path, phase)
            print(f"Actualizada {task_path.name} -> fase {phase}")
        
        # Acumular para actualizar archivo de fase
        if phase not in phase_tasks:
            phase_tasks[phase] = []
        phase_tasks[phase].append(task_id)
    
    # Actualizar archivos de fase
    update_phase_files(phase_tasks, phase_dir)
    
    # Crear resumen
    summary_path = Path("tasks/microtasks_summary_reassigned.md")
    with open(summary_path, 'w', encoding='utf-8') as f:
        f.write("# Resumen de Microtareas Reasignadas\n\n")
        f.write(f"Total: {len(tasks)} microtareas\n\n")
        for phase in sorted(phase_tasks.keys()):
            f.write(f"## Fase {phase}\n")
            f.write(f"Microtareas: {', '.join([f'{tid:04d}' for tid in sorted(phase_tasks[phase])])}\n")
            f.write(f"Cantidad: {len(phase_tasks[phase])}\n\n")
    
    print(f"\nResumen guardado en {summary_path}")

if __name__ == '__main__':
    main()

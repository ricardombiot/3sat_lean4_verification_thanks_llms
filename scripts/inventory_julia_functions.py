#!/usr/bin/env python3
"""
Script para inventariar funciones de archivos .jl en docs/original_julia/src
Genera un listado de funciones con su archivo y dependencias aproximadas.
"""

import os
import re
import sys
from pathlib import Path

def extract_functions(filepath: Path) -> list[dict]:
    """Extrae nombres de funciones de un archivo .jl."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Patrones para definiciones de función en Julia
    patterns = [
        r'^\s*function\s+(\w+)\s*\(',          # function nombre(
        r'^\s*(\w+)\s*\([^)]*\)\s*=',           # nombre(...) =
        r'^\s*(\w+)\s*\([^)]*\)\s*where',       # nombre(...) where
        r'^\s*(\w+)\s*\([^)]*\)\s*::',          # nombre(...) ::
    ]
    functions = []
    lines = content.split('\n')
    for i, line in enumerate(lines):
        for pattern in patterns:
            m = re.search(pattern, line.strip())
            if m:
                name = m.group(1)
                # Filtrar nombres que son keywords o muy cortos
                if len(name) > 1 and not name.startswith('#'):
                    functions.append({
                        'name': name,
                        'line': i + 1,
                        'file': str(filepath)
                    })
                break
    return functions

def find_imports(filepath: Path) -> list[str]:
    """Encuentra importaciones y includes en el archivo."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    imports = []
    # includes
    includes = re.findall(r'include\s*\(\s*["\'](.+?)["\']\s*\)', content)
    imports.extend(includes)
    # using
    usings = re.findall(r'using\s+([\w\.]+)', content)
    imports.extend(usings)
    # import
    imports2 = re.findall(r'import\s+([\w\.]+)', content)
    imports.extend(imports2)
    return imports

def main():
    src_root = Path('docs/original_julia/src')
    if not src_root.exists():
        print("Error: No se encuentra docs/original_julia/src")
        sys.exit(1)

    # Recorrer todos los archivos .jl
    all_functions = []
    file_imports = {}
    for jl_file in src_root.rglob('*.jl'):
        rel_path = jl_file.relative_to(src_root)
        print(f"Procesando {rel_path}...")
        funcs = extract_functions(jl_file)
        imports = find_imports(jl_file)
        file_imports[str(rel_path)] = imports
        for f in funcs:
            all_functions.append(f)

    # Generar reporte
    print(f"\nTotal de funciones encontradas: {len(all_functions)}")
    print("\n=== RESUMEN POR ARCHIVO ===")
    summary = {}
    for f in all_functions:
        file = f['file']
        summary[file] = summary.get(file, 0) + 1

    for file, count in sorted(summary.items()):
        print(f"{file}: {count} funciones")

    # Guardar detalles en un archivo CSV para análisis posterior
    import csv
    with open('julia_functions_inventory.csv', 'w', newline='') as csvfile:
        fieldnames = ['file', 'function', 'line']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for f in all_functions:
            writer.writerow({
                'file': f['file'],
                'function': f['name'],
                'line': f['line']
            })

    print("\nInventario guardado en 'julia_functions_inventory.csv'")

    # Imprimir algunas funciones de ejemplo
    print("\n=== ALGUNAS FUNCIONES EJEMPLO ===")
    for f in all_functions[:20]:
        print(f"{f['file']}:{f['line']} - {f['name']}")

if __name__ == '__main__':
    main()

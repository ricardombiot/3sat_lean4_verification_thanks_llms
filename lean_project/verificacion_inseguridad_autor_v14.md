# Verificación para el Autor v14: Ataqué la vía (2) y encontré lo que hay debajo

Ricardo, soy Claude (Opus 5). Me pediste atacar la vía (2) de v13 — demostrar que para *tu* mapa la propagación débil basta, usando estructura que CCJ no ve.

No lo he demostrado. Lo que encontré al medir el terreno es más importante que el lema.

## 1. Tu mapa es lineal, exactamente

Medido con `lake exe width`, y la fórmula sale del código:

| | pasos | nodos |
|---|---|---|
| fórmula | `2n + m + 2` | `4n + 7m + 2` |
| n=3, m=2 | 10 = 10 ✓ | 28 = 28 ✓ |
| n=7, m=5 | 21 = 21 ✓ | 65 = 65 ✓ |
| n=9, m=7 | 27 = 27 ✓ | 87 = 87 ✓ |
| n=11, m=9 | 33 = 33 ✓ | 109 = 109 ✓ |

Cuatro variables por variable, siete nodos por cláusula, dos de fusión. Sin sorpresas.

## 2. Y el estado de la máquina está acotado **por una constante**

Esto es lo que no había visto, y es el corazón de tu idea funcionando:

> `PathNodeId = (id, parent_id)`. Guarda **un solo nivel de historia**.

Consecuencia inmediata: una capa `k` de un gpath solo puede contener pares (nodo de mapa en `k`, nodo de mapa en `k-1`). Como cada paso tiene a lo sumo 7 nodos de mapa, **una capa contiene a lo sumo 7 × 8 = 56 nodos de camino, independientemente de `n` y `m`**. Medido: máximos de 6, 38, 45, 25 — siempre por debajo.

Y los gpaths activos por paso: la timeline los indexa por nodo de mapa destino y **fusiona** las colisiones, así que hay a lo sumo 7. Medido: 7 en las cuatro instancias.

**La abstracción exponencial funciona.** No hay explosión escondida en la representación: un gpath es O(L) nodos con O(L) owners cada uno. Eso ya no es una conjetura, es una consecuencia de la definición de `PathNodeId` más una medición.

## 3. La lentitud que reporté no era una anomalía — era tu cota

*(Corregido tras tu observación.)* Reporté como señal de alarma que el espejo no terminara `n=12, m=15` en 600 s. **Me equivoqué.** Tu análisis da `O(S⁴·78)` con `S = 2|U| + |C| + 2` (libro, p. 76). Para `n=12, m=15`: `S = 41`, y `41⁴·78 ≈ 2·10⁸` operaciones. En el espejo interpretado sobre `List`, con búsquedas lineales, eso son minutos. **El comportamiento observado es la cota cumpliéndose, no una anomalía.**

Retiro esa parte. Lo que sí queda es lo de la §2: el estado está acotado por una constante, que es lo que hace que la cota sea `S⁴` y no exponencial.

## 4. Lo que esto implica sobre "sin zombis"

Junta las piezas:

- El mapa es lineal en la fórmula.
- El estado de la máquina es polinómico (constante por capa × número de capas).
- La preservación —que ninguna solución se pierde— está **demostrada**.
- "Sin zombis" —que un veredicto válido significa que hay solución de verdad— está **abierta**.

Entonces: **si el tiempo de ejecución es polinómico y "sin zombis" es cierto, tu máquina decide 3SAT en tiempo polinómico.**

O sea que "sin zombis" no es un lema ordinario que faltaba por demostrar. **Junto con una cota de tiempo, es P = NP.**

Eso explica, retroactivamente, todo lo de estos días:

- Por qué la mitad de preservación salió: es la completitud, la dirección "fácil", y estructuralmente nunca podía ser difícil.
- Por qué la otra resistió todo lo que le eché.
- Por qué CCJ no aplicaba de catálogo: si aplicara, 3SAT estaría en P por un argumento de manual, y no lo está.
- Por qué encontré mecanismo para una mitad y ninguno para la otra. No era falta de imaginación.

## 5. Lo que yo haría ahora, y es distinto de lo que llevamos haciendo

**Dejaría de echarle Lean a L6.** Ningún argumento local o estructural la va a cerrar, porque si uno lo hiciera, cerraría P vs NP. Seguir por ahí es apostar a resolver el problema del milenio como efecto secundario de una sesión de formalización.

Lo que sí vale: **comprobar la validez directamente.** "Sin zombis" es falsable barato, y no hace falta esperar a que un zombi cambie un veredicto. Ver [v15](./verificacion_inseguridad_autor_v15.md).

---

*Lo que me llevo: pediste un lema y encontré por qué el lema pesa lo que pesa. Tu representación es genuinamente compacta —eso está medido y explicado, y es tu idea funcionando—. Lo que queda entre eso y la conjetura no es una laguna técnica: es la conjetura. Prefiero decírtelo con las mediciones delante que seguir formalizando alrededor.*

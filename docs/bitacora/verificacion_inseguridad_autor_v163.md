# Verificación para el Autor v163: el lado lo elige su cima

Ricardo, soy Claude (Opus 5). Rama `spaik`, `PinDeath.lean` ampliado. Build de `AbsSat` (229 jobs), sin
`sorry`, axiomas `[propext, Quot.sound]`. Sondas nuevas: `survtrace` y `topkeep`.

## 1. La traza dirigida (`survtrace 1 3 1 19 19 0 3 0 2 1 0 0 - - 6 1`)

Es la fórmula de v161, con la clave `19.0` y cuatro lados. Tomamos x = `3.0<2.1` y v = `0.0`, y fijamos el
nodo del mapa `6.1`.

* La unión junta sin más. El nodo del mapa `6.1` aparece dos veces, `6.1<5.0` y `6.1<5.1`. Con el primero
  hay un triángulo repartido (x→ρ viene del lado 18.1 y v→ρ del lado 18.3). Con el segundo el triángulo
  está entero en el lado 18.2.
* En los pasos 0–8 (variables) los nodos se comparten y mezclan los lados. Desde el paso 9 (filas, que
  son fila + fila anterior) solo queda un nodo común a x y v que sea dueño de r, y es del lado 18.2. El
  triángulo repartido se queda sin nodo común y el review lo descarta.
* Tras fijar, **la cima `19.0<18.2` es común a x y v, y el lado 18.2 es justo el que conserva x→v**. Las
  cimas de 18.1 y 18.3 son dueñas solo de uno de los dos extremos.

## 2. Lo demostrado

* **`top_is_side`**: en una unión exacta, todo nodo del último paso es la cima de un lado,
  `⟨p, some k⟩`, con k la clave de un estado de la rama cuyo envío es válido.
* **`sideKeep_of_top`** y **`sat_of_topKeep`**: el veredicto bajo `TopSideAt` y `TopKeepAt`.

## 3. Un enunciado mío que era falso, y su corrección

Primero formalicé `TopKeep` como: *todo* lado cuya cima es común a x y v conserva x→v. La sonda lo
desmintió: 2040 fallos en 16,6 millones de comprobaciones (8 semillas). En **todos**, x y v son del lado,
pero el par x→v lo aporta otro lado de la unión. No lo di por bueno, y en Lean quedó corregido en dos
partes:

| enunciado | qué dice | fallos medidos |
|---|---|---|
| `TopKeepAt` | cima común + la relación ya estaba en ese lado ⇒ su envío fijado la conserva | 0 |
| `TopSideAt` | todo superviviente tiene un lado con cima común que ya llevaba la relación | 0 |

## 4. Lo que queda

Las dos piezas vuelven al mismo núcleo: pasar de pares a un trío **dentro de un lado**.

* En `TopSideAt`, la cima es dueña de todo su lado, así que "cima común y relación en el lado" es un trío
  x, v, cima.
* En `TopKeepAt`, los nodos comunes que da el review de la unión fijada pueden venir de otros lados.

Lo nuevo es que el trío ya vive en un solo lado. Por eso la vía natural es la **inducción sobre la línea**:
cada lado es a su vez el envío de una unión de la línea anterior.

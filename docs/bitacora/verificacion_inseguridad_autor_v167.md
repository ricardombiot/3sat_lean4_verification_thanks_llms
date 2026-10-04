# Verificación para el Autor v167: la regla de la cima, por recorte al lado — y el soporte montado

Ricardo, soy Claude (Opus 5). Este informe sigue a v166 y cubre toda la etapa de `ImprovesCima`. Rama
`spaik`, módulo `ImprovesCima.lean`. El build de `AbsSat` (232 jobs) pasa sin `sorry`, con axiomas
`[propext, Quot.sound]`.

## 0. Resumen

* **La regla cambió de forma**, y por una razón de fondo: la versión de v166 (cláusulas de cierre
  escritas a mano) **no cerraba**. Con una regla existencial, dos relaciones pueden certificar cimas
  distintas, y entonces la regla de agregación del soporte —dos miembros de la familia necesitan un
  testigo común— no se deja demostrar.
* **La forma nueva**: para cada cima, recortar la unión a lo que el lado de esa cima lleva y revisar el
  recorte hasta su punto fijo. Una relación se conserva si sigue viva en la familia de alguna cima.
  Esa familia **está cerrada por construcción**: es un estado de la propia máquina.
* **El núcleo está demostrado**: una cima buena da un soporte del envío de su lado, y con él el envío
  fijado sigue vivo. Sin hipótesis.
* Queda **enchufar**: producir la cima buena para el lado elegido y cerrar la ruta C.

## 1. Por qué la forma anterior no cerraba

La de v166 pedía, además de la cadena y de que el lado llevara el par, un testigo por paso, un padre, un
hijo y el enlace. Lo demostré todo (`fam_witness`, `fam_par`, `fam_son`, `fam_link`, `fam_closure`) y
también que un camino real las cumple. Pero el soporte necesita una cosa más: dados **dos** miembros de
la familia, un testigo común de los dos. Y ahí la forma existencial se rompe:

> Una relación viva tiene *alguna* cima buena. Dos relaciones distintas pueden tener cimas distintas.
> Entonces no hay una tabla única donde buscar el testigo común.

La forma universal ("toda cima que ambos extremos alcanzan debe ser buena") **no sirve**: borraría pares
de caminos reales. Es el mismo fallo que ya medimos en v163 (`topkeep`, 2040 pares ajenos). No es un
detalle técnico: es la razón por la que la regla tiene que ser existencial.

Un caso sí se salva solo, y resultó clave: **cuando uno de los extremos es la cima de un lado**, la cima
certificada solo puede ser esa. Un nodo `⟨p, clave⟩` existe únicamente en su lado (`side_of_top`), y un
envío tiene exactamente un nodo en su paso nuevo (`sent_top`).

## 2. La regla nueva

> **Regla de la cima.** Para cada cima `t`: recorta la unión a las relaciones que **el lado de `t`**
> lleva en su tabla, en los dos sentidos, y que en pasos vecinos ese lado enlaza como padre e hijo.
> Revisa el recorte hasta el punto fijo. Una relación `a → b` se conserva si sigue viva en la familia de
> alguna cima, y esa familia es un estado vivo.

Tres cosas que la hacen funcionar:

* **El test no mira el estado.** Solo mira los lados. Por eso una pasada lo resuelve, y por eso la
  familia, al acabar, no contiene nada que el lado no lleve.
* **La familia es un estado de la máquina.** Es el review aplicado a un recorte, así que tiene sus
  invariantes y su soporte (`LinkedChain.sup_self`), sin pedir nada más.
* **Los enlaces padre-hijo también se recortan.** Sin eso, el padre y el hijo del soporte quedarían en
  las tablas de la unión y no en las del lado.

**No pierde soluciones** (`cimaOk_of_chain`): un camino real vive en un lado, así que ese lado lleva
todos sus pares y enlaza sus vecinos; el recorte no lo toca, el review lo conserva, y un estado que
contiene una cadena sana está vivo.

**Coste.** Una revisión agresiva por cada cima, en lugar de una búsqueda de cadena por cada par. Es
más barato que la forma anterior, y no cambia el orden de la máquina. Lo que sí hace falta es que la
máquina conserve los lados de la última unión mientras revisa.

## 3. Lo demostrado

### 3.1 La cima nombra el lado

| pieza | qué dice |
|---|---|
| `sent_top` | un envío tiene un solo nodo en su paso nuevo: su propia cima |
| `side_of_top` | un lado que contiene la cima `⟨p, clave⟩` **es** el envío de esa clave (las claves de una línea son distintas) |
| `carries_in_side` | lo que "algún lado lleva" con esa cima es una relación de **ese** envío |
| `linked_in_side` | lo mismo para los enlaces padre-hijo |

### 3.2 La familia

| pieza | qué dice |
|---|---|
| `keeps_famFix` | la familia solo quita |
| `ChainSound_famFix` | conserva una cadena que el lado lleva |
| `restOk_restAll` | cuando el recorte se estabiliza, **todo lo que queda pasa el test** |
| `restTest_of_famFix` | y sigue pasándolo tras el review |
| `side_of_famFix` | leído en el lado: toda relación de la familia es del envío del lado, en ambos sentidos, y en pasos vecinos uno de sus enlaces |
| `adj_famFix`, `sons_restAll` | la familia tiene los invariantes de un estado de la máquina |

### 3.3 El soporte

| pieza | qué dice |
|---|---|
| `sup_famFix` | **la familia tiene soporte: sus propias tablas** (es un punto fijo del review) |
| `sup_of_famSide` | ese soporte **es un soporte del envío del lado**: cobertura, agregación y simetría son de la familia; dueños, padre e hijo son lo que el test garantiza |
| `valid_pinned_of_famSide` | con ese soporte, **el envío fijado sigue vivo** — la conclusión que pide `TopValidAt` |
| `valid_pinned_of_goodFor` | la lectura entera desde **una sola cima buena** |

### 3.4 La máquina

| pieza | qué dice |
|---|---|
| `cimaOk_filterAllCima` | fijar y revisar deja siempre la regla satisfecha: toda relación viva tiene cima buena |
| `sons_filterAllCima` | los invariantes de hijos sobreviven al review completo de una unión y a sus fijados |
| `keeps_agg_filterAllCima` | el review nuevo es un estrechamiento del viejo, así que lo demostrado para `Improves` se transporta |
| `AOk_filterAllCima` | un soporte sobrevive a fijar y revisar |

### 3.5 Una limpieza que salió sola

Todo lo demostrado de la pasada —solo quita, no pierde soluciones, un soporte sobrevive, los invariantes
de hijos sobreviven, su punto fijo deja el test satisfecho— **nunca miraba cuál era el test**. Lo
generalicé (`prunePair` / `pruneNode` / `pruneSweep`), y ahora la regla de la cima y el recorte al lado
son dos instancias de la misma pasada. El módulo pasó de 1340 a 1080 líneas.

## 4. Lo que queda

Nada de esto pide demostrar algo nuevo; es enchufar:

1. **Producir la cima buena para el lado elegido.** `cimaOk_filterAllCima` da alguna; cuando un extremo
   es la cima del lado, `side_of_top` + `sent_top` fuerzan que sea esa misma. El lado lo elige
   `side_top_alive`, que ya está.
2. **Alimentar los invariantes de la unión filtrada** (contexto del lector, SMP/PMS/SN, `NotRoot`), que
   salen del `MInv` de la unión por `Keeps` con lo ya demostrado (§3.4).
3. **Cerrar `TopValidAt` para `ImprovesCima`** y, por la ruta C ya demostrada
   (`TopValidAt ⟹ ValidSideAt ⟹` invariante de validez hereditaria `⟹` veredicto), el veredicto.

## 5. Lo que esto significa, y lo que no

* Lo que quedará demostrado es el veredicto de **`ImprovesCima`**, la máquina con la regla. De
  `Improves` seguimos teniendo lo de siempre: no pierde soluciones, su veredicto leído con certificado
  nunca es erróneo, y las medidas, que no fallan nunca, pero no una demostración.
* La regla no cambia ningún resultado en lo medido: en esas familias no borra nada, porque la condición
  ya se cumplía.

## 6. Commits de esta etapa

`60c6376`, `c7c9f80`, `100aa6a`, `baa42c6`, `f4727d3`, `ea48753`, `8349606`, `1a5ada8`, `9cbb2be`,
`377c3db`, `2fb732c`, `00e5852`, `0ba64d4`, `64b749a`, `bab0047`, `25e264f`, `9e68de9`, `6be09b7`.

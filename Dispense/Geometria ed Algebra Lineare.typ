#import "@preview/theorion:0.3.3": *
#import "@preview/itemize:0.2.0" as el

#import cosmos.rainbow: *

#show: show-theorion
#show: el.default-enum-list

#set text(lang: "it")
#set par(justify: true)
#set page(numbering: "I", footer: [], header: context {
  if counter(page).display() != "I" {
    if calc.even(counter(page).get().at(0)) {
      align(
        left,
        [#{ counter(page).display() } - _Geometria ed Algebra Lineare_],
      )
    } else {
      align(
        right,
        [_Geometria ed Algebra Lineare_ - #{ counter(page).display() }],
      )
    }
  }
})

#align(center, heading(outlined: false, [Geometria ed Algebra Lineare]))
#align(
  center,
  [Andrea Giurgola - Prof. Emanuele Rodaro \ Ingegneria Elettronica, Politecnico di Milano],
) \

#set heading(numbering: "1.1.")
#set-theorion-numbering("1.1")
#outline(title: [Indice])

#pagebreak()
#counter(page).update(1)
#set page(numbering: "1")

= Spazi vettoriali

Tra insiemi si possono svolgere delle *operazioni*, le quali si distinguono in *interne* od *esterne*, e *unarie* o *binarie*.
#definition(
  title: [Operazione],
  [Sia $cal(P)$ una funzione. $cal(P)$ si dice un'operazione:
    - _binaria_ se $cal(P)$: $AA_1 times AA_2 -> AA_3$
    - _unaria_ se $cal(P)$: $AA -> AA$
    - _esterna_ se il suo risultato è esterno agli insiemi operandi
    - _interna_ se il suo risultato è contenuto negli insiemi operandi, i quali coincidono tra loro
  ],
)

#definition(
  title: [Campo vettoriale],
  [
    Sia $(KK, plus.circle, times.circle)$ una struttura. Essa si dice _campo vettoriale_ se:
    - $plus.circle$ e $times.circle$ sono due operazioni binarie interne
    - $plus.circle$ e $times.circle$ soddisfano le proprietà commutativa, associativa e distributiva di $times.circle$ su $plus.circle$
    - esiste l'elemento neutro e l'inverso per entrambe le operazioni
  ],
)
#note-box([Gli inversi di un'operazione sono *unici*.])

I campi si distinguono in:
- *finiti*: presentano un numero di elementi limitato (es. $FF_2$ ("interi modulo 2") $= {\[0\], \[1\]}$)
- *infiniti*: presentano un numero infinito di elementi (es. $(RR, +, dot), (QQ, +, dot), (CC, +, dot)$)
- *non-campo*: una struttura che non soddisfa tutti i requisiti necessari per essere campo (es. $(NN, +, dot)$ è un non-campo in quanto non ha inversi additivi o moltiplicativi.)

#definition(
  title: [Vettore],
  [Un vettore è un $n$-upla ordinata di punti, i quali appartengono allo stesso insieme. Dati $A in RR^2$ e $BB in RR^2$, si denota come $(A, B), A B, arrow(A B), underline(A B), B - A, ...$],
)
Un vettore ha un *verso*, una *direzione* e una *norma*, ossia la sua lunghezza (denotata come $norm(A B)$). \
Due vettori si dicono *equipollenti* se con una traslazione posso sovrapporli, dunque se hanno norma, direzione e verso coincidenti.


#definition(
  title: [Spazio vettoriale],
  [
    Sia $(KK, +, dot, 0, 1)$ un campo vettoriale. $V$ si dice _spazio vettoriale_ sul campo $KK$ se:
    - $V$ è un insieme di vettori
    - all'interno di $V$ si può svolgere l'operazione binaria interna di _somma_, la quale soddisfa le proprietà associativa e commutativa, ha elemento neutro ($cal(O) = (0, 0, 0)$) e inverso ($exists w in V : v + w = 0, forall v in V$).
    - all'interno di $V$ si può svolgere l'operazione binaria esterna di _prodotto per uno scalare_ ($KK times V -> V$), la quale soddisfa le proprietà distributiva di $dot$ su $+$ e associativa e ha l'$1$ come elemento neutro
  ],
)

In generale $(RR^n, +, dot, RR)$ è uno spazio vettoriale.

== Operazioni tra vettori

La *somma tra vettori* è un'operazione binaria interna che, dati due vettori, restituisce un altro vettore con le componenti sommate tra loro membro a membro.
$
  underbracket(vec(x_1, x_2, x_3) + vec(y_1, y_2, y_3), "Somma su" RR^3) = vec(x_1 + y_1, x_2 + y_2, underbracket(x_3 + y_3, "Somma su" RR)), forall x_n, y_n in RR
$
Il *prodotto per uno scalare* è un'operazione binaria esterna che, dato un vettore e uno scalare, restituisce un nuovo vettore con ogni componente moltiplicata per il dato scalare.
$ k dot vec(a, b, c) = vec(k a, k b, k c) $
Il *prodotto scalare standard* è un'operazione binaria esterna valida solo nel campo reale ($RR^3 times RR^3 -> RR$) che, dati due vettori, restituisce uno scalare che corrisponde alla somma tra i prodotti delle componenti.
$ vec(a, b, c) dot vec(d, e, f) = a dot d + a dot e + c dot f $
Se il prodotto scalare tra due vettori è nullo, allora i due vettori sono perpendicolari fra loro.

== Indipendenza lineare e basi

#definition(
  title: [Span lineare],
  [
    Si dice _span lineare_ l'insieme di tutte le combinazioni lineari di un insieme di vettori.
    $
      cal(L)(v_1, ..., v_k) := {w : w = a_1 v_1 + ... + a_k v_k, forall a_n in RR}
    $
  ],
)
#definition(
  title: [Generatore di vettori],
  [
    L'insieme $(v_1, ..., v_n)$ di $(V, +, dot, KK)$ si dice _generatore di vettori di V_ se $cal(L)(v_1, ..., v_n) = V$. Perciò $V$ si dice _finitamente generato_.
  ],
)
#definition(
  title: [Dipendenza ed indipendenza lineare],
  [
    I vettori $v_1, ..., v_n$ si dicono _linearmente dipendenti_ se $exists x_i in KK : x_1 v_1 + ... + x_n v_n = cal(O), x_i != 0$, dunque se esiste una combinazione lineare non banale di $cal(O)$. Se ciò non succede, allora i vettori si dicono _linearmente indipendenti_.
  ],
)
#proposition(
  title: [Condizione di dipendenza lineare],
  [
    $v_1, ..., v_n$ linearmente dipendenti se e solo se uno dei vettori è combinazione lineare degli altri.
  ],
)
#proof([
  $c_1 v_1 + ... + c_n v_n = 0$ per qualche $c_i != 0$. Supponiamo $c_1 = 0$ \
  $=> v_1 + (c_1^(-1) c_2) dot v_2 + ... (c_1^(-1) c_n) dot v_n = 0 => v_1 = -(c_1^(-1) c_2) dot v_2 - ... - (c_1^(-1) c_n)v_n in cal(L)(v_2, ..., v_n)$ \
  $=> v_1 = d_2 v_2 + ... + d_n v_n => d_2 v_2 + ... + d_n v_n - v_1 = cal(O) =>$ combinazione lineare di $cal(O) != underline(0)$
])

#proposition(
  title: [Unicità di combinazioni lineari di vettori linearmente indipendenti],
  [
    Se $v_1, ..., v_n$ sono linearmente indipendenti, allora $u = c_1 v_1 + ... + c_n v_n$, con $c_i in KK$ unici.
  ],
)
#proof([
  Supponiamo che $c_1 v_1 + ... c_n v_n = u = d_1 v_1 + ... + d_n v_n$. Allora
  \ $(c_1 - d_1)v_1 + ... (c_n - d_n)v_n = cal(O) => c_i - d_i = 0 => c_i = d_i$.
])#definition(
  title: [Base],
  [
    La _base finita_ di uno spazio vettoriale $(V, +, dot, KK)$ finitamente generato è un insieme di vettori $v_1, ..., v_n in V$ ordinato tale per cui:
    - genera $V$: $V = cal(L)(v_1, ..., v_n)$
    - i vettori sono linearmente indipendenti: $c_1, ..., c_n$ sono unici e il vettore $(c_1, ..., c_n) in KK^n$ si dice _vettore delle coordinate_ di $v in V$ rispetto alla base $B = {v_1, ..., v_n}$ e si indica $[v]_B = (c_1, ..., c_n)$
  ],
)
#note-box([
  $v |-> [v]_B, forall v in V$ è una funzione biunivoca. Infatti, per isomorfismo delle coordinate, possiamo dire $u display(op(|->, limits: #true)_(x_B)) [u]_B$ e, contemporaneamente, $[u]_B display(op(|->, limits: #true)_(x^(-1)_B)) u$.
])

Fissiamo ora uno spazio vettoriale $(V, +, dot, KK)$ finitamente generato.
#lemma(
  title: [Lemma di scarto],
  [
    Se $v_1, ..., v_n$ sono linearmente dipendenti, allora $cal(L)(v_1, ..., v_n) = cal(L)(v_1, ..., v_(n - 1))$.
  ],
) <spv:lsc>
#proof([
  Poiché $v_1, ..., v_n$ linearmente dipendenti allora, per esempio, $v_1 = c_2 v_2 + ... + c_n v_n$ con $c_i in KK$ opportuni. Dimostriamo prima che $cal(L)(v_2, ..., v_n) subset.eq cal(L)(v_1, ..., v_n)$. \
  $<=> w = d_2 v_2 + ... + d_n v_n = 0 v_1 + d_2 v_2 + ... + d_n v_n => w in cal(L)(v_1, ..., v_n)$ \
  Dimostriamo ora che $cal(L)(v_1, ..., v_n) subset.eq cal(L)(v_2, ..., v_n)$. \
  $<=> w = d_1 v_1 + ... + d_n v_n = d_1 (c_2 v_2 + ... + c_n v_n) + d_2 v_2 + ... + d_n v_n = (d_1 c_2 + d_2) v_2 + ...$ \ #"        " $+ (d_1 c_n + d_n) v_n => w in cal(L)(v_2, ..., v_n)$
])
#lemma(
  title: [Lemma di aggiunta],
  [
    Siano $v_1, ..., v_l in V$ linearmente indipendenti con $v_(l + 1) in.not cal(L)(v_1, ..., v_l)$. Allora $v_1, ..., v_l, v_(l + 1)$ sono linearmente indipendenti.
  ],
) <spv:lag>
#proof([
  $v_1, ..., v_l, v_(l + 1)$ linearmente indipendenti $<=> c_1 v_1 + ... c_l v_l + c_(l + 1) v_(l + 1) = cal(O)$. \
  Supponiamo, per assurdo, che $c_(l + 1) != 0 => -c_(l + 1) v_(l + 1) = display(sum^l_(i = 1) c_i v_i) => v_(l + 1) = display(sum^l_(i = 1) - c_i / c_(l + 1) dot v_i)$ \
  $<=> v_(l + 1) in cal(L)(v_1, ..., v_l) =>$ assurdo. Dunque $c_(l + 1) = 0 => v_1, ... v_l, v_(l + 1)$ linearmente indipendenti.
])
#theorem(
  title: [Esistenza di una base],
  [
    Se lo spazio $(V, +, dot, KK)$ è finitamente generato, allora esiste una base finita.
  ],
)
#pagebreak()
#proof([
  Sia $V = cal(L)(v_1, ..., v_n)$ \
  Se $v_1, ..., v_n$ sono linearmente indipendenti, allora sono una base. \
  Se $v_1, ..., v_n$ sono linearmente dipendenti, allora posso eliminare un vettore per il @spv:lsc il quale posso scrivere come combinazione lineare degli altri $=> cal(L)(v_1, ..., v_n) = cal(L)(v_1, ..., v_(n - 1))$. Se $v_1, ..., v_(n - 1)$ sono ancora linearmente dipendenti, allora ripeto lo scarto di un vettore finché non ottengo un insieme di vettori linearmente indipendenti, i quali, allora, costituiranno una base
])
#lemma(
  title: ["Troppi vettori sono linearmente dipendenti"],
  [
    Se $cal(L)(v_1, ..., v_n) = V$ allora $w_1, ..., w_m in V$ con $m > n$ sono linearmente dipendenti.
  ],
) <spv:ltd>
#theorem(
  title: [Teorema della dimensione],
  [
    Siano $B_1 = {v_1, ..., v_m}, B_2 = {w_1, ..., w_n}$ due basi dello spazio $(V, +, dot, KK)$ finitamente generato. Allora $n = m$.
  ],
)
#proof([
  Supponiamo, per assurdo, che $n > m$. Allora $w_1, ..., w_n$ sono linearmente dipendenti secondo il @spv:ltd, il che è un assurdo perché, per ipotesi, compongono una base, quindi sono linearmente indipendenti. Dunque, necessariamente, $n = m$.
])
#definition(
  title: [Dimensione di uno spazio vettoriale],
  [
    La dimensione di uno spazio vettoriale $(V, +, dot, KK)$ finitamente generato, indicata come $dim(V)$, corrisponde al numero di elementi di una qualunque base $B$ dello spazio.
  ],
)
#note-box([
  Sia $dim(V) = n$. Allora:
  - $w_1, ..., w_m$ con $m > n$ sono linearmente dipendenti
  - Se $u_1, ..., u_n$ sono linearmente indipendenti, allora ${u_1, ..., u_n}$ è una base
  - Se $s_1, ..., s_n$ sono generatori, allora ${s_1, ..., s_n}$ sono una base, poiché, se sono generatori, sono anche linearmente indipendenti. Infatti, se non lo fossero, per il @spv:lsc potremmo estrarre una base ${s_1, ..., s_l}$ con $l < n$, il che però non avrebbe senso dal momento che tutte le basi hanno lo stesso numero di elementi
])
#proposition(
  title: [Isomorfismo delle coordinate di una combinazione lineare],
  [
    Siano $(V, +, dot, KK), B = {v_1, ..., v_n}, u_1, u_2$, uno spazio vettoriale, la sua base e due vettori in $V$. Allora $forall a, b in KK, [a dot u_1 + b dot u_2]_B = a[u_1]_B + b[u_2]_B$. Ossia, le coordinate di una combinazione lineare di vettori corrisponde alla combinazione lineare delle coordinate di vettori.
  ],
)
#proof([
  Sia $n = 2 => [u_1]_B = vec(c_1, c_2), [u_2]_B = vec(d_1, d_2)$.
  $<=> u_1 = c_1 v_1 + c_2 v_2, u_2 = d_1 v_1 + d_2 v_2$ \
  $<=> a u_1 + b u_2 = a c_1 v_1 + a c_2 v_2 + b d_1 v_1 + b d_2 v_2 = v_1 (a c_1 + b d_1) + v_2 (a c_2 + b d_2)$ \
  $<=> [a u_1 + b u_2]_B = vec(a c_1 + b d_1, a c_2 + b d_2) = a vec(c_1, c_2) + b vec(d_1, d_2) = a[u_1]_B + b[u_2]_B$
])

#pagebreak()

= Geometria nel piano e nello spazio

In generale, per $AA_1$ si intende l'*insieme dei punti sulla retta affine*, per $AA_2$ l'*insieme dei punti sul piano affine* e per $AA_3$ l'*insieme dei punti nello spazio affine*.

#definition(
  title: [Insiemi di vettori in $AA_1, AA_2, AA_3$],
  [Fissato un punto $O$ di origine, denotiamo con $V_0^1$ l'_insieme dei vettori della retta affine_ con origine $O$, $V_0^2$ l'_insieme dei vettori del piano affine_ con origine $O$, e $V_0^3$ l'_insieme dei vettori dello spazio affine_ con origine $O$.],
)
#note-box([Ad ogni vettore corrisponde un vettore centrato nell'origine a lui equipollente. ($exists! O B' ~ A B, forall A B in RR^2$). Ogni punto appartenente al retta/piano/spazio affine può essere individuato da un vettore centrato nell'origine.])

Per sommare due vettori centrati nello stesso punto, si utilizza la *regola del parallelogramma*.
$ O A + O B := O C, O C ~ A B $
Si dimostra dunque che $(V_0^2, +)$ è un gruppo commutativo:
- vale la proprietà associativa: $O A + (O B + O C) = (O A + O B) + O C$
- vale la proprietà commutativa: $O A + O B = O B + O A$
- esiste l'elemento neutro: $exists cal(O) = O O : O A + O O = O A$
- esiste l'inverso: $(O, A) = -(O, -A)$ \

Il prodotto per uno scalare si definisce come $RR times V_0^2 -> V_0^2$. Il vettore risultato del prodotto di $v in V_0^2$ per uno scalare $t in RR$ è il vettore con uguale direzione, norma moltiplicata per t e verso concorde per $t >= 0$ e discorde per $t <= 0$.

== Sistemi di riferimento

Per poter descrivere un punto $P$ su una retta è necessario avere un *sistema di riferimento*. Se fissiamo un qualsiasi punto $O$ sulla retta come *origine* del sistema e un qualsiasi vettore $v$ che indica la direzione del sistema di riferimento, otteniamo $R(O, v)$. Dunque il punto $P$ può essere individuato tramite il vettore $O P in V_0^1 = 2 dot v$, dove il $2$ rappresenta l'unica coordinata del punto.

Nel caso del piano affine, bisogna aggiungere al sistema un secondo vettore $u$ che non sia parallelo a $v$ (ossia $v != t dot u, forall t in RR$), ottenendo quindi $R(O, v, u)$. \
Dato un qualsiasi punto $Q$ nel piano con coordinate $(2, 2)$, esso sarà individuato dal vettore \ $O Q in V_0^2 = 2 dot v + 2 dot u$, ossia come *combinazione lineare* tra $vec(v, u)$ e $vec(2, 2)$. Analogamente, nel caso dello spazio affine va introdotto un terzo vettore $w$ tale che $v, u, w$ non siano complanari (ossia $w != t dot v + s dot u, forall t, s in RR$).

Per poter semplificare i calcoli, si può introdurre un sistema di riferimento *ortonormale*, ossia con vettori lunghi $1$ e perpendicolari fra loro. Per esempio, ora è possibile calcolare la norma di un vettore utilizzando il teorema di Pitagora ($O A = (a, b, c), norm(O A)^2 = a^2 + b^2 + c^2$) oppure calcolare il coseno dell'angolo compreso tra due vettori ($O B = (d, e, f), cos theta = (O A dot O B)/(norm(O A) dot norm(O B))$).

== Rette e piani in $AA_3$

In generale, una retta è definita come l'insieme dei punti i cui vettori associati fissati nell'origine sono il risultato della somma tra un punto noto che appartiene alla retta e un *vettore direttore* moltiplicato per un parametro $t in RR$, dunque l'espressione è detta *equazione parametrica*.
#definition(
  title: [Retta in $AA_3$],
  [
    $
      r := {P : O P tilde.eq vec(x, y, z) = vec(x_0, y_0, z_0) + t vec(x_v, y_v, z_v), forall t in RR}
    $
  ],
)
#note-box([L'equazione parametrica di una retta non è unica in quanto il punto noto può variare.])
#definition(
  title: [Piano in $AA_3$],
  [
    $
      pi = {P : O P = vec(x, y, z) tilde.eq vec(x_0, y_0, z_0) + t vec(x_v, y_v, z_v) + s vec(x_u, y_u, z_u), v parallel.not u, forall t, s in RR}
    $
    dove ${v, u}$ è detta _base della giacitura del piano $pi$_.
  ],
)

== Equazioni cartesiane di piani

Nell'equazione parametrica di un piano sono espliciti sia i vettori direttori che il punto passante, mentre in un'*equazione cartesiana* $x, y, z$ sono coinvolti implicitamente.
$
  vec(x, y, z) = vec(1, -1, 1) t + vec(1, 1, -1) s + vec(1, 2, 0) <==> 2x + y - z - 4 = 0
$
Per passare dall'equazione parametrica a quella cartesiana, è necessario eliminare i parametri esprimendoli in funzione delle componenti. Mentre per tornare all'equazione parametrica, si scelgono due componenti per essere sostituite dai due parametri.
#definition(
  title: [Equazione cartesiana di un piano in $AA_3$],
  [
    $
      pi := {P : P in AA_3, P tilde.eq vec(x, y, z) in RR^3, a x + b y + c z + d = 0, a, b, c, d in RR}
    $
  ],
)
#note-box([Le equazioni cartesiane di un piano non sono uniche.])
#pagebreak()
I coefficienti $a, b, c, d$ hanno un significato geometrico. Infatti, supponendo $d = 0$ abbiamo che
$
  a x + b y + c z = 0 <=> vec(a, b, c) dot vec(x, y, z) = 0 => vec(a, b, c) perp vec(x, y, z)
$
Dunque il vettore $(a, b, c)$ rappresenta il *vettore direttore* del piano, il quale è perpendicolare ad ogni vettore appartenente al piano.

== Equazioni cartesiane di rette

#definition(
  title: [Equazione cartesiana di una retta in $AA_3$],
  [
    $
      r := {P : P in AA_3, P tilde.eq vec(x, y, z), cases(a x + b y + c z + d = 0, e x + f y + g z + h = 0), a, ..., h in RR }
    $
  ],
)
Abbiamo dunque che, in generale, una retta espressa in forma cartesiana è rappresentata dal risultato dell'*intersezione fra due piani*. \
Allo stesso modo del piano, per convertire un'equazione parametrica in una cartesiana, è necessario esprimere il parametro in funzione di $x, y, z$, mentre per effettuare il processo inverso si sceglie una tra le componenti per essere sostituita dal parametro.

== Posizioni reciproche di rette e piani

#definition(
  title: [Posizioni reciproche di rette in $AA_3$],
  [
    Siano $r, s in AA_3$ due rette. Esse sono tra loro:
    - _parallele_ se i loro vettori direttori sono paralleli
    - _incidenti_ se $r inter s != emptyset$
    - _complanari_ se esiste un piano che le contiene entrambe, quindi sono o parallele o incidenti
    - _perpendicolari_ se i loro vettori direttori sono perpendicolari
    - _sghembe_ se non sono complanari
  ],
)
#definition(title: [Posizioni reciproche di piani in $AA_3$], [
  Siano $pi_1, pi_2 in AA_3$ due piani. Essi sono tra loro:
  - _paralleli_ se i loro vettori direttori sono paralleli
  - _incidenti_ se $pi_1 inter pi_2 != emptyset$
  Siano $pi, r in AA_3$ un piano e una retta. Essi sono tra loro.
  - _paralleli_ se i loro vettori direttori sono perpendicolari
  - _incidenti_ se $pi inter r != emptyset$
])

#pagebreak()

= Matrici

#definition(title: [Matrice], [
  Si dice _matrice_ con $m$ righe ed $n$ colonne su campo $KK$ la funzione:
  $
    A: {1, ..., m} times {1, ..., n} -> KK => (i, j) |-> A(i, j) = a_(i j) in KK
  $
])
Una matrice $A$ con $m$ righe ed $n$ colonne è una "*tabella*" di $m$ righe ed $n$ colonne contenente elementi in un campo $KK$. $A_(i j)$ indica l'elemento alla riga $i$ e alla colonna $k$ ($1 <= i <= m, 1 <= j <= n$).
Un insieme di matrici di $m$ righe ed $n$ colonne su campo $KK$ è definito genericamente come
$
  MM_(m, n)(KK) := {A : A " " m a t r i c e, A_(i j) in KK, i = 1, ..., m, j = 1, ..., n }
$ \ \

Data una qualsiasi matrice $A in MM_(m, n)(KK)$ essa può essere vista come un insieme di righe o di colonne.
$
  mat(
    a_11, a_12, ..., a_(1n);
    a_21, a_22, ..., a_(2n);
    dots.v, dots.v, dots.down, dots.v;
    a_(m 1), a_(m 2), ..., a_(m n)
  ) -> mat(R_1; R_2; dots.v; R_n), (C_1 | C_2 | ... | C_m)
$

== Operazioni fra matrici

#definition(
  title: [Somma fra matrici],
  [
    Siano $A, B, C in MM_(m, n)(KK)$ tre matrici. \
    $A + B: MM_(m, n)(KK) times MM_(m,n)(KK) -> MM_(m,n)(KK) => (A, B) |-> C = A + B$ \ con $c_(i j) = a_(i j) + b_(i j), forall i = 1, ..., m, j = 1, ..., n$
  ],
)
La possibilità della somma rende $(MM_(m,n)(KK), +)$ un gruppo commutativo, dunque:
- valgono le proprietà associativa e commutativa
- esistono l'elemento neutro e l'inverso
$
  O_(m,n) = mat(0, ..., 0; dots.v, dots.down, dots.v; 0, ..., 0) => A + O_(m,n) = A, -A := mat(-a_11, ..., -a_(1n); dots.v, dots.down, dots.v; -a_(m 1), ..., -a_(m n)) => A + (-A) = O_(m,n)
$

#definition(
  title: [Prodotto per uno scalare di una matrice],
  [
    Siano $A, C in MM_(m,n)(KK), b in KK$ due matrici e un elemento del campo $KK$. \
    $b dot A: KK times MM_(m,n)(KK) -> MM_(m,n)(KK) => (b, A) |-> C = b dot A$ \
    con $c_(i j) = b a_(i j), forall i = 1, ..., m, j = 1, ..., n$
  ],
)
#pagebreak()
Il prodotto per uno scalare di una matrice possiede:
- proprietà distributiva di $dot$ su $+$
$
  c dot (A + B) = c dot A + c dot B, forall c in KK, forall A, B in MM_(m,n)(KK) \
  (c + d) dot A = c dot A + d dot A, forall c, d in KK, forall A in MM_(m,n)(KK)
$
- proprietà associativa
$
  (c dot d) dot A = c dot (d dot A) = d dot (c dot A), forall c,d in KK, forall A in MM_(m,n)(KK)
$
- opposto ed elemento neutro
$ A + (-A) = A + -1 dot A = O_(m,n), 1 dot A = A, forall A in MM_(m,n)(KK) $
#note-box([($MM_(m,n)(KK), +, dot, KK$) è uno spazio vettoriale.])

#definition(title: [Trasposizione di una matrice], [
  Sia $A in MM_(m,n)(KK)$ una matrice. \
  $A^t: MM_(m,n)(KK) -> MM_(n,m)(KK) => A |-> A^t$ \
  con $A_(i j) = (A^t)_(j i), forall i = 1, ..., m, j = 1, ..., n$
])
Considerati $forall A, B in MM_(m,n)(KK), forall c in KK$, la trasposizione ha le seguenti proprietà:
$ (A^t)^t = A, (A + B)^t = A^t + B^t, (c dot A)^t = c dot A^t $
#definition(title: [Matrice simmetrica], [
  Si dice _simmetrica_ la matrice $A$ tale per cui
  $ A = A^t => A in MM_(n,n)(KK) $
])
#definition(
  title: [Prodotto riga per colonna],
  [
    Siano $R in MM_(1,n)(KK), C in MM_(n,1)(KK), b in KK$ una riga e una colonna di una matrice. \
    $R dot C: MM_(1,n)(KK) times MM_(n,1)(KK) -> MM_(1,1)(KK) => (R, C) |-> b$ \
    con $R dot C = (r_1, ..., r_n) dot vec(c_1, dots.v, c_n) = display(sum^n_(k = 1)r_k c_k)$
  ],
)
Corrisponde esattamente al prodotto scalare fra due vettori. Più precisamente, dati due vettori $v, u$
$
  underbracket(v dot u, "Prodotto fra vettori") "      " underbracket(v^t dot u, "Prodotto riga per colonna")
$
#definition(title: [Prodotto tra matrici], [
  Siano $A in MM_(m,n)(KK), B in MM_(n,k)(KK), C in MM_(m,k)(KK)$ tre matrici. \
  $A dot B: MM_(m,n)(KK) times MM_(n,k)(KK) -> MM_(m,k)(KK) => (A, B) |-> C$ \
  con $c_(i j) = R_(A i) dot C_(B j), forall i = 1, ..., m, j = 1, ..., k$
])
Se $A in MM_(m,n)(KK)$, il prodotto tra matrici possiede le seguenti proprietà:
- $A dot e_k = C_k$ dove $e_k$ è il *vettore canonico*, ossia è nullo in tutte le righe eccetto per la $k$-riga, nel quale ha valore 1
- $A dot I_m = A$ dove $I_m = (e_1 | e_2 | ... | e_m) = delta_(i j) = cases(1 "se" i = j, 0 "se" i != j)$ ed $I_m$ è detta *matrice identità* o *delta di Kronecker*
- distributiva su $+$: siano $B, C in MM_(n,k)(KK)$, allora $A dot (B + C) = A dot B + A dot C$
- associativa: siano $B in MM_(n,k)(KK), C in MM_(k, p)(KK)$, allora $underbrace(A dot underbrace((B dot C), n times p), m times p) = underbrace(underbrace((A dot B), m times k) dot C, m times p)$
- $C dot D != D dot C, forall C, D in MM_(n,n)(KK)$
- $(A dot B)^t = B^t dot A^t$, con $B in MM_(n,k)(KK)$: qui è importante l'inversione degli operandi
- $A dot O_(n,k) = O_(m,k)$
#definition(title: [Matrice quadrata], [
  Si dice _matrice quadrata_ la matrice $A in MM_(n,n)(KK)$
])

= Sistemi lineari

#proposition(
  title: [Soluzione di sistemi lineari],
  [
    Un sistema lineare $A dot x = b$, con $A = (C_1 | ... | C_n)$, ha soluzione se e solo se $b in cal(L)(C_1, ..., C_n)$
  ],
)
#proof([$b in cal(L)(C_1, ..., C_n) <=> exists " " overline(x_1), ..., overline(x_n) in KK : b = overline(x_1) dot C_1 + ... + overline(x_n) dot C_n$. Quindi $vec(overline(x_1), ..., overline(x_n))$ risolve il sistema.])

L'insieme delle soluzioni del sistema lineare $A dot x = b$, con $A in MM_(m,n)(KK), b in MM_(m,1)(KK)$ si indica:
$ S o l(A, b) = {x in KK^n : A dot x = b} $
Se $b = underline(O)_m$ allora il sistema è detto *omogeneo*.
#definition(
  title: [Kernel di una matrice],
  [
    Sia $A in MM_(m,n)(KK)$. Allora $ker(A) = S o l(A, underline(O)_m)$, dove il $ker(A)$ è detto _nucleo di A_ o _kernel di A_.
  ],
)
#note-box([
  - $ker(A) != emptyset$. Infatti $A dot underline(O)_n = underline(O)_m$. Quindi $underline(O)_n in ker(A)$.
  - Se $v_1, ..._v_n$ in $(KK^m, +, dot, KK)$ con $n > m$, allora $v_1, ..., v_n$ sono linearmente dipendenti \ $=> ker(A) != {underline(0)}$ quindi $ker(A)$ dipende da almeno un parametro
])

== Mosse di Gauss

Le mosse di Gauss sono un algoritmo che permette di modificare una matrice o un sistema lineare preservandone l'insieme di soluzioni. Comprendono:
- scambio di righe
- sostituzione di una certa $R_i$ con $a dot R_i + c dot R_k$, con $a, c in KK, a != 0$
#proposition(
  title: [Conservazione delle soluzioni tramite le mosse di Gauss],
  [Le mosse di Gauss preservano $S o l(A)$],
)
#proof([È ovvio che la prima mossa preservi le soluzioni. \
  La seconda mossa porta ad avere un nuovo sistema. Infatti
  $
    (A | b) = #math.mat(augment: 1, ..(($R_1$, $b_1$), ($R_2$, $b_2$))) -> (B | d) = #math.mat(augment: 1, ..(($a dot R_1 + c dot R_2$, $a dot b_1 + c dot b_2$), ($R_2$, $b_2$)))
  $
  Sia $alpha in S o l(A, b) subset.eq S o l(B, d)$. Allora
  $
    cases(R_1 dot alpha = b_1, R_2 dot alpha = b_2) => cases(a dot R_1 dot alpha + c dot R_2 dot alpha = a b_1 + c b_2, R_2 dot alpha = b_2) <=> cases(alpha (a dot R_1 + c dot R_2) = a b_1 + c b_2, R_2 dot alpha = b_2)
  $
  Dunque $alpha in S o l(B, d)$. Quindi possiamo applicare la seconda mossa di Gauss al nuovo sistema.
  $
    cases(alpha (a dot R_1 + cancel(c_R_2)) - cancel(c R_2) dot alpha = a b_1 + cancel(c b_2) - cancel(c b_2), R_2 dot alpha = b_2) => cases(R_1 dot alpha = b_1, R_2 dot alpha = b_2) "se" a != 0
  $
  Dunque $alpha in S o l(A, b)$
])

#definition(
  title: [Matrice a scala],
  [
    Una matrice A è detta _a scala_ se è della forma:
    $
      mat(
        0, ..., 0, P_1, ..., ..., ..., ..., ...; 0, ..., ..., 0, ..., 0, P_2, ..., ...; dots.v, , , dots.down, , dots.down, , , dots.v; 0, ..., ..., ..., ..., ..., ..., 0, P_r;
        0, ..., ..., ..., ..., ..., ..., ..., 0
      )
    $
    con $P_1, ..., P_r != 0$ detti _pivot_
  ],
)
#theorem(title: [Riduzione a scala con mosse di Gauss], [
  Ogni matrice si può ridurre in una scala tramite le mosse di Gauss.
])
#note-box([Mosse diverse portano a matrici a scala diverse.])

== Algoritmo di Gauss

L'algoritmo di Gauss permette di risolvere sistemi lineari utilizzando le mosse di Gauss, e procede con i seguenti passi:
1. Sistemare il primo pivot perché sia a più sinistra possibile, individuando la prima colonna non nulla e una riga tale che $a_(i_1 j_1) != 0$
2. Si rendono con la seconda mossa di Gauss tutti i coefficienti sotto il primo pivot $0$
3. Si ripete l'algoritmo considerando la sottomatrice B che prende tutte le righe eccetto la prima e tutte le colonne fino a quella del pivot: se la matrice è vuota o già a scala, allora l'algoritmo è concluso

#definition(
  title: [Matrice a scala ridotta],
  [
    Una matrice ha la forma di _scala ridotta_ se è a scala, se tutti i pivot valgono 1 e se sopra ai pivot ci sono solo 0.
  ],
)

=== Algoritmo di Gauss-Jordan

L'algoritmo di Gauss-Jordan si fonda su quello di Gauss e lo estende per ottenere una matrice a scala ridotta. Procede come segue:
1. Si applica $G a u s s(A)$ alla matrice e poi si parte dall'ultimo pivot e si annullano tutti i valori sopra di esso con le mosse di Gauss
2. Se sopra i pivot ci sono valori diversi da 0, applico l'algoritmo alla sottomatrice che comprende tutti i pivot tranne quelli già sistemati, sennò vado al terzo punto
3. In ogni riga si divide ogni valore per il valore del pivot di tale riga. Quindi, l'algoritmo è concluso.


#definition(
  title: [Rango di una matrice],
  [
    Il _rango_ di una matrice A, indicato con $r k(A)$, corrisponde al numero di pivot della matrice a scala ridotta ottenuta da A.
  ],
)
#theorem(title: [Riduzione unica con l'algoritmo di Gauss-Jordan], [
  L'algoritmo di Gauss-Jordan genera un'unica matrice a scala ridotta.
])
#corollary([
  $r k(A)$ è il numero di pivot di una qualunque matrice a scala ottenuta da A.
])
#note-box([
  Sia $A in MM_(m,n)(KK)$. Allora $r k(A) <= m$ e $r k (A) <= n$. Dunque $r k(A) <= min{m, n}$
])

== Struttura dei sistemi lineari

#proposition(
  title: [Struttura di un sistema omogeneo],
  [
    Sia $A in MM_(m,n)(KK)$. Allora $ker(A) = cal(L)(v_1, ..., v_2) = {w = t_1v_1 + ... + t_s v_s : A dot v_i = 0, t_i in KK, s = n - r k(A)}$
  ],
)
Dunque abbiamo che $s$ rappresenta il numero minimo di parametri necessari a descrivere il kernel di A in forma parametrica, dal momento che potrebbero non esserci abbastanza equazioni per trovare un'unica soluzione. In genere i parametri vengono assegnati alle variabili che non presentano un pivot nella loro colonna.

#proposition(
  title: [Proprietà di un sistema lineare],
  [
    Sia $A in MM_(m,n)(KK)$. Allora:
    1. se $A dot v_1 = b_1, A dot v_2 = b_2$, quindi con $v_1 in S o l(A, b_1), v_2 in S o l(A, b_2)$, allora $ A dot c v_1 + A dot d v_2 = c b_1 + d b_2 <=> A dot (c v_1 + d v_2) = c b_1 + d b_2, forall c, d in KK $
    2. se $alpha in S o l(A, b)$ allora $S o l(A , b) = { beta = alpha + v : v in ker(A) }$
  ],
)
#proof([
  1. $A dot (c v_1 + d v_2) = A dot c v_1 + A dot d v_2 = c underbrace((A dot v_1), b_1) + d underbrace((A dot v_2), b_2) = c b_1 + d b_2$ \ \
  2. $A dot alpha = b, A dot beta = b => A dot alpha - A dot beta = underline(0) => A dot (alpha - beta) = underline(0) => alpha - beta in ker(A) \ => alpha = beta + underbrace((alpha - beta), in ker(A)) => alpha in beta + ker(A), S o l(A, b) subset.eq alpha + ker(A)$ \ Viceversa, se $alpha = beta + v, v in ker(A)$ allora $A dot beta = A dot (alpha + v) = A dot alpha + A dot v = b + underline(0) = b$ \ $=> alpha in S o l(A, b)$
])

#theorem(title: [Struttura di un sistema lineare], [
  Sia $A in MM_(m,n), A dot alpha = b$. Allora $S o l(A, b) = alpha + ker(A)$.
]) <ssl:ssl>
#theorem(
  title: [Teorema di Rouché-Capelli],
  [
    Sia $A in MM_(m,n)(KK)$. Allora il sistema $A dot x = b$:
    1. ha soluzione se e solo se $r k(A) = r k(A|b)$
    2. se $exists alpha in S o l(A, b)$ allora $S o l(A, b) = alpha + ker(A) = {beta in KK^n : beta = alpha + t_1 v_1 + ... + t_s v_s,$ $forall t_i in KK, v_i in ker(A), s = n - r k(A)}$
  ],
)
#proof([Poiché abbiamo dimostrato che le mosse di Gauss non cambiano $S o l(A, b)$, è sufficiente dimostrare il teorema per una qualsiasi matrice a scala. \
  1. $(A|b) display(op(-->, limits: #true)^("Gauss")_("Jordan")) R = (A'|b') => "va notato che" r k(A) <= r k(A|b)$. Se indichiamo con $x$ l'ultimo pivot (il quale si trova nel vettore $b$), allora sappiamo che il sistema ha soluzione se e solo se $x = 0$, ossia $S o l(A, b) != emptyset <=> r k(A) = r k(A') = r k(A'|b') = r k(A|b)$
  2. Segue dal @ssl:ssl.
])
#corollary([
  - Se $m >= n =>$ esiste un'unica soluzione $<=> r k(A) = n$
  - Se $m < n$ (_sistema sottodeterminato_) $=> S o l(A, b)$ dipende da almeno un parametro, quindi se $KK$ è infinito, allora ci sono infinite soluzioni $=> ker(A) != {underline(0)}$
  - Se $b = underline(0), r k(A) = n => S o l(A, b) = {underline(0)}$
  - Se $r k(A) = m => S o l(A) != emptyset$
]) <ssl:ctrc>
#note-box([
  $S o l(A, b) subset.eq KK^n$ si può rappresentare in forma:
  - _cartesiana_: ${x = (x_1, ..., x_n) in KK^n, k in KK : (a_1, ..., a_n)x = k}$
  - _parametrica_: ${beta = (a_1, ..., a_n) + t_1 (b_1, ..., b_n) + t_2(c_1, ..., c_2), forall t_1, t_2 in KK}$
])
#theorem(
  title: [Teorema di Cramer],
  [
    Sia $A in MM_(n,n)(KK), A dot x = b$ un sistema quadrato. Allora esiste un'unica soluzione $<=> r k(A) = n$.
  ],
) <ssl:tcr>
#proof([
  Per il @ssl:ctrc, $S o l(A, b) != emptyset$ e la soluzione è unica, dunque $r k(A) = n$.
])

== Inversa di una matrice
#definition(
  title: [Inverse di una matrice],
  [
    Sia $A in MM_(n,n)(KK)$. A si dice _invertibile_ e possiede una:
    - _inversa destra_ se $exists D in MM_(n,n)(KK) : A dot D = I_n$
    - _inversa sinistra_ se $exists S in MM_(n,n)(KK) : S dot A = I_n$
    Se $D$ ed $S$ esistono, allora coincidono. È necessario distinguere le inverse perché $A dot S != S dot A$.
  ],
)

#theorem(title: [Caratteristiche di una matrice invertibile], [
  Sia $A in MM_(n,n)(KK)$. Allora:
  1. $A$ è invertibile
  2. $A dot x = b$ ha un'unica soluzione
  3. $r k(A) = n$
  4. $exists "inversa destra" D$
  5. $exists "inversa sinistra" S$
])
#proof([
  - $1. => 2.$ : $A dot x = b$ è risolto da $x = A^(-1) dot b => A dot (A^(-1) dot b) = (A dot A^(-1)) dot b = I_n dot b = b$. \ Siano ora $alpha_1, alpha_2 in S o l(A, b)$, dunque $A dot alpha_1 = b, A dot alpha_2 = b => A dot alpha_1 = A dot alpha_2$ \ $<=> A dot alpha dot A^(-1) = A dot alpha dot A^(-1) <=> I dot alpha_1 = I dot alpha_2 => alpha_1 = alpha_2$
  - $2. => 3.$ : Segue dal @ssl:tcr
  - $3. => 4.$ : $D = (d_1 | d_2 | ... | d_n) in MM_(n,n)(KK) => A dot D = (A dot d_1 | A dot d_2 | ... | A dot d_n) = I_n$ \ $<=> A dot d_i = e_i$. Bisogna risolvere $n$ sistemi lineari quadrati e, visto che $r k(A) = n$ per il teorema di Cramer, allora $d_i$ esiste ed è unica. Per poterli risolvere contemporaneamente posso dire che $(A | e_1 | ... | e_n) = (A | I) display(op(-->, limits: #true)^("Gauss")_("Jordan")) ( I | d_1 | ... | d_n) = (I | D) = (I | A^(-1))$
])
#definition(
  title: [Matrici simili],
  [
    Due matrici quadrate $A, B in MM_(n,n) (KK)$ si dicono _simili_ se esiste una matrice $P$ invertibile tale che $B = P^(-1) dot A dot P$, quindi $B tilde A$.
  ],
)
La relazione di similitudine è una relazione di equivalenza quindi è:
- *riflessiva*: $A tilde A$, infatti $A = I^(-1) dot A dot I$
- *simmetrica*: $B tilde A <=> A tilde B$, infatti se $B = P^(-1) dot A dot P$, allora, moltiplicando per $P dot P^(-1)$, abbiamo $P dot B dot P^(-1) = P dot P^(-1) dot A dot P dot P^(-1) = A$
- *transitiva*: $A tilde B, B tilde C <=> A tilde C$, infatti $A = P^(-1) dot B dot P$ e $B = Q^(-1) dot C dot Q$, quindi $A = P^(-1) dot (Q^(-1) dot C dot Q) dot P = (Q dot P)^(-1) dot C dot (Q dot P) = H^(-1) dot C dot H$


== Sottospazi vettoriali

Fissato $(V, +, dot, KK)$ come spazio vettoriale, allora $(U, +, dot, KK)$ con $U subset.eq V$ è anch'esso uno spazio vettoriale? Sì, ma con il *restringimento* delle operazioni di somma e prodotto su $U$. Dunque \ $+: U times U |-> U$ e $dot.c: KK times U |-> U$.
#definition(
  title: [Sottospazio vettoriale],
  [
    Sia $U subset.eq V$. $U$ è un _sottospazio vettoriale_ se in $U$ sono valide le stesse operazioni di $V$.
  ],
)
#proposition(
  title: [Criterio dei sottospazi vettoriali],
  [
    Sia $U subset.eq V$. Allora $U$ è un sottospazio vettoriale se $c_1 u_1 + c_2 u_2 in U, forall u_1, u_2 in U, forall c_1, c_2 in KK$.
  ],
) <ssl:csv>
#note-box([
  $U = emptyset$ è il più piccolo sottospazio vettoriale, detto _banale_.
])

#proposition(
  title: [Kernel come sottospazio],
  [
    Sia $A in MM_(m,n)(KK). ker(A) subset.eq KK^n$ è un sottospazio vettoriale di $(KK^n, +, dot, KK)$.
  ],
)
#proof([
  Per la @ssl:csv, $ker(A)$ è un sottospazio vettoriale se \
  $c_1 v_1 + c_2 v_2 in ker(A), forall v_1, v_2 in ker(A), forall c_1, c_2 in KK$. Inoltre \
  $c_1 v_1 + c_2 v_2 in ker(A) <=> A dot (c_1 v_1 + c_2 v_2) = underline(0) => c_1 dot underbrace(A dot v_1, = " " underline(0)) + c_2 dot underbrace(A dot v_2, = " " underline(0)) = c_1 dot underline(0) + c_2 dot underline(0) = underline(0)$
  $=> c_1 v_1 + c_2 v_2 in ker(A) => ker(A)$ è un sottospazio vettoriale.
])
#note-box([
  Dal @ssl:ssl $ker(A) = cal(L)(v_1, ..., v_s)$ con $s = n - r k(A)$. Infatti $v_1, ..., v_s$ è una base \
  $=> dim(ker(A)) = n - r k(A)$
])

=== Struttura dei sottospazi vettoriali
Sia $(V, +, dot, KK)$ con $dim(V) = n < +infinity$.
#proposition(
  title: [Span come sottospazio],
  [
    Se $u_1, ..., u_l in V$ allora $U = cal(L)(u_1, ..., u_l)$ è un sottospazio vettoriale di $V$.
  ],
)
#proof([
  Siano $v_1, v_2 in U$ con $U = cal(L)(u_1, ..., u_l)$. Allora $v_1 = display(sum^l_(i = 1) a_i u_i), v_2 = display(sum^l_(i = 1) b_i u_i)$. \
  $forall c, d in KK, c dot v_1 + d dot v_2 = c dot display(sum^l_(i = 1) a_i u_i) + d dot display(sum^l_(i = 1) b_i u_i) = display(sum^l_(i = 1) (c a_i + d b_i) dot u_i in cal(L)(u_1, ..., u_l))$. \
  Per la @ssl:csv, $U$ è un sottospazio vettoriale di $V$.
])
#definition(
  title: [Sottospazio affine],
  [
    Un _sottospazio affine_ di V è l'insieme $A = v_0 + W = {v_0 + w : w in W}$ con $v_0 in V,$ \ $W$ sottospazio di $V$.
  ],
)
#theorem(
  title: [Teorema del completamento],
  [
    Sia $U$ un sottospazio di $V$, $u_1, ..., u_l in U$ linearmente indipendenti. Allora si può estendere così da avere una base di $U$. In simboli: $U = cal(L)(u_1, ..., u_l, u_(l + 1), ..., u_m) "con" m = dim(U), m <= dim(V)$.
  ],
) <ssv:cpl>
#pagebreak()
#proof([
  Sia $B_l = {u_1, ..., u_l} subset.eq U$.
  1. Se $cal(L)(B_l) = cal(L)(u_1, ..., u_l) = U$ allora $B_l$ è una base di $U$
  2. Se $cal(L)(B_l) subset.eq.not U$, allora consideriamo $u_(l + 1) in U \\ cal(L)(B_l)$ con $U \\ cal(L)(B_l) != emptyset$. Per il @spv:lag, $u_1, ..., u_l, u_(l + 1)$ sono linearmente indipendenti. Considero dunque $B_(l + 1) = B_l union {u_(l + 1)}$, e se $cal(L)(B_(l + 1)) != U$ allora itero l'aggiunta fino a che $l + 1 = m = dim(U)$.
])
#proposition(
  title: [Criterio dimensionale di un sottospazio],
  [
    Sia $U$ un sottospazio di $V$. Se $dim(U) = dim(V)$ allora $U = V$. In particolare, se $u_1, ..., u_n$ sono linearmente indipendenti con $n = dim(V)$ allora sono base di $V$.
  ],
)
#proof([
  Sia $U = cal(L)(u_1, ..., u_n) => u_1, ..., u_n$ linearmente indipendenti. Se $U subset.eq.not V$, per il @spv:lag, $u_(n + 1) in V \\ U$, tale che $u_1, ..., u_n, u_(n + 1)$ sono linearmente indipendenti, il che è un assurdo poiché $dim(V) = n$, quindi $dim(U) <= n => U = V$.
])

Un sottospazio $U = cal(L)(u_1, ..., u_m) subset.eq KK^n$ può essere visto come matrice. Dunque, per esempio \
$
  U = cal(L)(vec(1, 1, 1), vec(1, 2, 3)) => A = (u_1 | u_2) = mat(1, 1; 1, 2; 1, 3), B = A^t = mat(1, 1, 1; 1, 2, 3)
$

=== Calcoli di sottospazi con le matrici

Se consideriamo $A in MM_(m,n)(KK)$, può risultare utile studiare $cal(L)(R i g(A)) subset.eq KK^n$ e $cal(L)(C o l(A)) subset.eq KK^m$.
#proposition(
  title: [Indipendenza lineare dei vettori riga di una matrice],
  [
    Se $A$ è a scala, le righe non nulle $R_1, ..., R_k$ sono vettori linearmente indipendenti di $KK^n$. \
    Inoltre, le mosse di Gauss non cambiano lo span delle righe.
  ],
)
#proof([
  Sia $A = vec(R_1, dots.v, R_m) display(op(-->, limits: #true)^"2ª mossa"_(a != 0)) vec(a R_1 + b R_2, dots.v, R_m) = A'$. \
  Per il @spv:lsc, $cal(L)(a R_1 + b R_2, R_1, R_2, ..., R_m) = cal(L)(R_1, R_2, ..., R_m) = cal(L)(R i g(A))$, in quanto il primo vettore si può esprimere come combinazione lineare di $R_1$ e $R_2$. \
  Sempre per il @spv:lsc, $cal(L)(a R_1 + b R_2, R_1, R_2, ..., R_m) = cal(L)(a R_1 + b R_2, R_2, ..., R_m) = cal(L)(R i g(A'))$, poiché $R_1$ si può esprimere come combinazione lineare del primo vettore di $R_2$.
  Dunque $cal(L)(R i g(A)) = cal(L)(R i g(A'))$.
])
#corollary([
  $dim(cal(L)(R i g(A))) = r k(A)$, quindi la dimensione del sottospazio vettoriale delle righe di $A$ è pari al numero di pivot della matrice $A$ ridotta a scala.
])
#note-box([
  $dim(cal(L)(C o l(A))) subset.eq KK^m dim(cal(L)(R i g(A))) subset.eq KK^n$ non sono comparabili.
])
#theorem(title: [Equivalenza tra rango per righe e rango per colonne], [
  $ dim(cal(L)(C o l(A))) = dim(cal(L)(R i g(A))) = r k(A) $
])
#warning-box([$cal(L)(C o l(A))$ non si preserva quando riduco $A$ a scala.])

#proposition(
  title: [Estrazione di base con riduzione a scala],
  [
    Siano $B = (v_1 | ... | v_n)$ una matrice con $v_1, ..., v_n in KK^m$, $I = {j_1, ..., j_k}$ l'insieme degli indici di colonna dei pivot di $B$ ridotta a scala. Allora $B = {v_j_i, j_i in I}$ è base di $cal(L)(v_1, ..., v_n)$.
  ],
)

=== Operazioni su sottospazi vettoriali

#proposition(
  title: [Intersezione di sottospazi vettoriali],
  [
    Siano $U_1, U_2 display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Allora $U_1 inter U_2 display(op(subset.eq, limits: #true)^(s.s.v.)) V$
  ],
)
#proof([
  Siano $u_1, u_2 in U_1 inter U_2$. Allora, per ipotesi e per la @ssl:csv \
  $c_1 u_1 + c_2 u_2 in U_1$ e $c_1 u_1 + c_2 u_2 in U_2, forall c_1, c_2 in KK => c_1 v_1 + c_2 v_2 in U_1 inter U_2$
])
#warning-box([
  In generale, l'unione di due sottospazi vettoriali non è anch'essa un sottospazio, a meno che \ $U_1 subset.eq U_2$ o $U_2 subset.eq U_1$.
])
#definition(
  title: [Somma di sottospazi vettoriali],
  [
    Siano $H, W display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Allora $H + W = {v =h + w : h in H, w in W}$.
  ],
)
Banalmente, si ha che $H subset.eq H + W, W subset.eq H + W$ e $H union W subset.eq H + W$.
#proposition(
  title: [Span della somma di due sottospazi vettoriali],
  [
    Siano $H = cal(L)(h_1, ..., h_k), W = cal(L)(w_1, ..., w_m)$. Allora $H + W = cal(L)(h_1, ..., h_k, w_1, ..., w_m)$.
  ],
)
#proof([
  Sia $V subset.eq H + W$. Quindi $v = h + w$ dove $h = display(sum^k_(i = 1)) a_i h_i, w = display(sum^m_(i = 1)) b_i w_i$. Dunque \
  v = $display(sum^k_(i = 1)) a_i h_i + display(sum^m_(i = 1)) b_i w_i => v in cal(L)(h_1, ..., h_k, w_1, ..., w_m)$ \
  $v = h + w => v in H + W => H + W = cal(L)(h_1, ..., h_k, w_1, ..., w_m)$
])

#note-box([
  Se $B_H$ e $B_W$ sono basi di $H$ e $W$ allora $H + W = cal(L)(B_H, B_W)$. Dunque $H + W$ è un sottospazio con generatori ${B_H, B_W}$.
])
#warning-box([
  In generale, l'unione di vettori linearmente indipendenti non è linearmente indipendente.
])

#lemma(
  title: [Unione di basi estese],
  [
    Siano $H, W display(op(subset.eq, limits: #true)^(s.s.v.)) V$ con $B_(H inter W) = {u_1, ..., u_l}, B_W = {u_1, ..., u_l, w_(l + 1), ..., w_k}$ ottenuta estendendo $B_(H inter W)$ e $B_H = {u_1, ..., u_l, h_(l + 1), ..., h_m}$. Allora $B_H union B_W$ sono linearmente indipendenti.
  ],
) <ssl:ube>
#proof([
  Sia $U display(op(subset.eq, limits: #true)^(s.s.v.)) H$. Allora $u = display(sum^l_(i = 1)) a_i u_i, h = display(sum^m_(i = 1)) b_i h_i, w = display(sum^k_(i = 1))c_i w_i$. \
  $u + h + w = cal(O) <=> u + h = -w$. $u + h in H$ poiché $U subset.eq H$. Dunque $w in H inter W => w = display(sum^k_(i = 1)) d_i u_i$. \
  $=> display(sum^l_(i = 1)) (a_i + d_i)u_i + display(sum^m_(i = 1)) b_i h_i = cal(O)$. È una combinazione lineare di ${u_1, ..., u_l, h_(l + 1), ..., h_m} = B_H$. Dunque, devono essere linearmente indipendenti, il che é possibile solo con $b_i = 0$. \
  $=> display(sum^l_(i = 1)) a_i u_i + display(sum^k_(i = 1)) c_i w_i = cal(O)$. È una combinazione lineare di ${u_1, ..., u_l, w_(l + 1), ..., w_k} = B_W$. Dunque, sono linearmente indipendenti se $a_i = 0, c_i = 0 => B_H union B_W$ linearmente indipendenti.
])
#corollary([
  Se $H inter W = {cal(O)}$ e $B_H, B_W$ sono basi di $H$ e $W$ rispettivamente, allora $B_H union B_W$ sono linearmente indipendenti. In particolare $B_(H + W) = B_H union B_W$.
]) <ssl:cube>
#definition(
  title: [Somma diretta di due sottospazi],
  [
    Siano $H, W display(op(subset.eq, limits: #true)^(s.s.v.)) V$ con $H inter W = {cal(O)}$. Allora $H + W$ è anche detta _somma diretta di $H$ e $W$_ e si indica $H plus.circle W$.
  ],
)
#theorem(
  title: [Formula di Grassmann],
  [
    Siano $H, W display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Allora $dim(H + W) = dim(H) + dim(W) - dim(H inter W)$.
  ],
)
#proof([
  Sia $B_U = {u_1, ..., u_l}$ una base di U. Essa la posso estendere a $B_W = {u_1, ..., u_l, w_(l + 1), ..., w_k}$ e $B_H = {u_1, ..., u_l, h_(l + 1), ..., h_m}$
  Allora, per il @ssl:ube, $B_H union B_W$ sono linearmente indipendenti, ma è anche base di $H + W = cal(L)(B_W union B_H)$. Quindi $dim(H + W) = dim(B_W union B_H) = k + m - l = dim(H) + dim(W) - dim(H inter W).$
])
= Applicazioni lineari

#definition(
  title: [Applicazione o funzione lineare],
  [
    Siano $(V, +, dot, KK), (W, +, dot, KK)$ due spazi vettoriali sullo stesso campo. Allora la funzione \
    $T: V -> W$ si dice _lineare_ se $T(v + u) = T(v) + T(u), T(c dot v) = c dot T(v), forall v, u in V, forall c in KK$.
  ],
)
Si nota che $v + u$ e $c dot v$ sono operazioni in $V$, mentre $T(v) + T(u)$ e $c dot T(v)$ sono operazioni in $W$.

#proposition(
  title: [Criterio di linearità],
  [
    Sia $T: V -> W$ una funzione. Essa è lineare se \
    $
      T(c_1 v_1 + c_2 v_2) = c_1 T(v_1) + c_2 T(v_2), forall c_1, c_2 in KK, forall v_1, v_2 in V
    $
  ],
)
Se dominio e codominio coincidono, allora la funzione è detta *endomorfismo*. Se, invece, la funzione è biunivoca, allora è detta *isomorfismo*.

Le funzioni lineari possiedono le seguenti proprietà:
- $T(cal(O)_V) = cal(O)_W$: infatti $T(cal(O)_V) = T(0 dot cal(O)_V) = 0 dot T(cal(O)_V) = cal(O)_W$
- $T(-v) = -T(v)$
- $T(display(sum^k_(i = 1)) c_i v_i) = display(sum^k_(i = 1)) c_i T(v_i)$
- $T: V -> W, L: W -> Z => (L compose T)(v) = L(T(v))$. Se $L, T$ lineari, anche $L compose T$ lineare
- Se $U display(op(subset.eq, limits: #true)^(s.s.v.)) V$ allora anche $T(U) display(op(subset.eq, limits: #true)^(s.s.v.)) W$
- Se $H display(op(subset.eq, limits: #true)^(s.s.v.)) W$ allora anche $T^(-1)(H) display(op(subset.eq, limits: #true)^(s.s.v.)) V$

#note-box([
  Una funzione $T: KK^n -> KK^m$ tale per cui $T vec(x_1, dots.v, x_n) = vec(f_1(x_1, ..., x_n), dots.v, f_m (x_1, ..., x_n))$ è lineare se e solo se $f_i (x_1, ..., x_n)$ è un polinomio di primo grado omogeneo, ossia senza termine noto.
])

#proposition(title: [Funzione lineare come span lineare], [
  Se $U = cal(L)(u_1, ..., u_k)$ allora $T(U) = cal(L)(T(u_1), ..., T(u_k))$.
])
#proof([
  Sia $u in U$. Dunque $u = display(sum^k_(i = 1)) c_i u_i$ \
  $=> T(u) = T(display(sum^k_(i = 1)) c_i u_i) = display(sum^k_(i = 1)) c_i T(u_i) in cal(L)(T(u_1), ..., T(u_k))$ \
  Sia $w in cal(L)(T(u_1), ..., T(u_k))$. Dunque $u = display(sum^k_(i = 1)) d_i u_i$ \
  $=> w = display(sum^k_(i = 1)) d_i T(u_i) = T(display(sum^k_(i = 1)) d_i u_i) = T(u) => w = T(u)$
])
#note-box([
  $T$ è suriettiva se e solo se $dim(T(V)) = dim(W) => T(V) display(op(subset.eq, limits: #true)^(s.s.v.)) W$.
])
#warning-box([
  In generale, la controimmagine di un vettore $T^(-1)({w})$ non è un sottospazio vettoriale. Infatti, se lo fosse avremmo $u_1, u_2 in T^(-1)(W) => u_1 - u_2 in T^(-1)(W)$, dunque $w = T(u_1 - u_2) =$ \
  $T(u_1) - T(u_2) = w - w = cal(O)$, il che è un assurdo se $w != cal(O)_W$.
])

== Nucleo di un'applicazione lineare

#definition(
  title: [Kernel di una funzione lineare],
  [
    Sia $T: V -> W$ lineare. Allora $ker(T) = T^(-1)({cal(O)_W}) = {v in V : T(v) = cal(O)_W}$
  ],
)
#pagebreak()
#proposition(
  title: [Proprietà del nucleo di una funzione lineare],
  [
    Sia $T: V -> W$. Allora valgono le seguenti proprietà:
    1. $ker(T) display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Infatti $T(c_1 v_1 + c_2 v_2) = c_1 T(v_1) + c_2 T(v_2) = c_1 dot underline(0) + c_2 dot underline(0) = underline(0),$\ $forall v_1, v_2 in ker(T), forall c_1, c_2 in KK$.
    2. $ker(T) = {cal(O)_V} => T$ iniettiva
    3. Se $T^(-1)(w) != emptyset, forall w in W$ e $alpha in T^(-1)(w)$ allora $T^(-1)(w) = alpha + ker(T)$. Questo è detto anche _teorema della fibra_.
    4. $T^(-1)(H) = cal(L)(alpha_1, ..., alpha_l) plus.circle ker(T)$, dove $H = cal(L)(h_1, ..., h_l) subset.eq W, alpha_i in T^(-1)(h_i)$. Infatti ${alpha_1, ..., alpha_l}$ sono linearmente indipendenti, poiché controimmagini di $H$, dunque possiamo anche dire che $T^(-1)(H)$ è un sottospazio vettoriale e una sua base è ${alpha_1, ..., alpha_l} union B_(ker(T))$
  ],
)
#proof([
  2. Siano $T$ iniettiva e $v in ker(T)$. Allora $T(v) = cal(O)_W = T(cal(O)_V) => v = cal(O)_V$. \ Siano ora $ker(T) = {cal(O)_V}, v_1, v_2 in V$ tali che $T(v_1) = T(v_2) => T(v_1) - T(v_2) = cal(O)_W$. \ Poiché $T$ è lineare, $T(v_1 - v_2) = cal(O)_W => v_1 - v_2 in ker(T)$. \ Per ipotesi, $ker(T) = {cal(O)_V} => v_1 - v_2 = cal(O)_V <=> v_1 = v_2$
  3. Siano $alpha, beta in T^(-1)(w)$. $T(beta - alpha) = T(beta) - T(alpha) = w - w = cal(O)_W => beta - alpha in ker(T)$ \ $=> beta = alpha + (beta - alpha) => beta in alpha + ker(T)$
])

Consideriamo una matrice $A in MM_(m,n)(KK)$ e la funzione lineare associata $L_A: KK^n -> KK^m$. Allora valgono le seguenti proprietà:
- $(L_B compose L_A)(x) = L_B (L_A (x)) = L_B (A dot x) = B dot (A dot x) = (B dot A) dot x = L_(B dot A)(x)$ \ dove $B in MM_(s,m)(KK)$ e $L_B: KK^m -> KK^s$
- $ker(L_A) = {v in KK^n : L_A (v) = A dot v = underline(0)} = ker(A)$
- $L_A^(-1)(b) = {x in KK^n : b = L_A (x) = A dot x} = S o l(A, b) = alpha + ker(A) = alpha + ker(L_A)$ con $b in KK^m$
- $L_A^(-1)(H) = cal(L)(alpha_1, ..., alpha_l) plus.circle ker(A)$ con $H = cal(L)(b_1, ..., b_l)$ e $alpha_i in L_A^(-1)(b_i)$
- $L_A (U) = cal(L)(L_A (u_1), ..., L_A (u_s))$ con $U display(op(subset.eq, limits: #true)^(s.s.v.)) KK^n$ e $U = {u_1, ..., u_s}$.
- $L_A (KK^n) = L_A (cal(L)(e_1, ..., e_n)) = cal(L)(L_A (e_1), ..., L_A (e_n)) = cal(L)(A dot e_1, ..., A dot e_n) = cal(L)(C o l(A))$ \ $=> dim (L_A (KK^n)) = r k(A)$

#theorem(
  title: [Teorema di nullità più rango],
  [
    Sia $T: V -> W$ lineare con $dim(V) = n$. Allora $dim(V) = dim(T(V)) + dim(ker(T))$.
  ],
) <apl:npr>
#proof([
  Sappiamo che $ker(T) display(op(subset.eq, limits: #true)^(s.s.v.)) V, ker(T) = cal(L)(u_1, ..., u_l), dim(ker(T)) = l$. \
  Per il @ssv:cpl, possiamo completare ${u_1, ..., u_l, v_(l + 1), ..., v_n}$ come base di $V$. \
  Poiché $T$ è lineare, $T(V) = cal(L)(underbrace((T(u_1), ..., T(u_l)), = cal(O)_W), T(v_(l + 1)), ..., T(v_n)) = cal(L)(T(v_(l + 1)), ..., T(v_n))$ \
  Dimostriamo dunque che ${T(v_(l + 1)), ..., T(v_n)}$ sono linearmente indipendenti. \
  $<=> display(sum^n_(s = l + 1)) a_s T(v_s) = cal(O)_W <=> T(display(sum^n_(s = l + 1))a_s v_s) => display(sum^n_(s = l + 1)) a_s v_s in ker(T) => display(sum^n_(s = l + 1)) a_s v_s = display(sum^l_(i = 1)) b_i u_i$ \
  $=> display(sum^n_(s = l + 1)) a_s v_s + display(sum^l_(i = 1)) (-b_i v_i) = cal(O)_V$. Poiché $v_s, u_i in B_V => b_1 = ... = b_l = a_(l + 1) = ... = a_s = 0$ \
  $=> T(v_(l + 1)), ..., T(v_n)$ linearmente indipendenti $<=> {T(v_(l + 1)), ..., T(v_n)}$ base di $V$ \
  $=> dim(T(V)) = n - l = dim(V) - dim(ker(T)) <=> dim(V) = dim(T(V)) + dim(ker(T))$
])
#corollary([
  Sia $A in MM_(m,n)(KK)$. Allora $dim(ker(A)) = n - r k(A)$
])
#proof([\
  Per le proprietà di funzioni lineari con matrice associata, $dim(L_A (KK^n)) = dim(C o l(A)) = r k(A)$. \
  Per il @apl:npr, $n = dim(KK^n) = dim(L_A (KK^n)) + dim(ker(A)) = r k(A) + dim(ker(A))$ \
  $=> dim(ker(A)) = n - r k(A)$
])

Il teorema di nullità più rango comporta delle conseguenze:
- Se $T: V -> W$ è iniettiva, allora $dim(V) = dim(T(V))$ il che è $<= dim(W)$, dal momento che $ker(T) = {cal(O)} => dim(ker(T)) = 0$
- Se $T$ è suriettiva, allora $dim(V) >= dim(W)$, poiché $T(V) = W$ quindi $dim(V) = dim(W) + underbrace(dim(ker(T)), >= 0)$
#note-box([
  Se $T$ è iniettiva e ${v_1, ..., v_n}$ è una base di $V$ allora $T(V) = cal(L)(T(v_1), ..., T(v_n))$ e, poiché $dim(T(V)) = n = dim(V)$, ${T(v_1), ..., T(v_n)}$ è una base di $T(V)$.
])
#proposition(title: [Isomorfismo della funzione inversa], [
  Sia $T: V -> W$ lineare. Allora $T^(-1): W -> V$ è un isomorfismo.
])
#theorem(title: [Biunivocità di una funzione lineare], [
  Sia $T: V -> W$ lineare. Se $dim(V) = dim(W)$, allora $T$ è biunivoca.
]) <apl:bfl>
#proof([
  Se $T$ è iniettiva, allora $ker(T) = {cal(O)} => dim(ker(T)) = 0, dim(V) = dim(T(V)),$ \ $dim(T(V)) <= dim(W)$. Però, $dim(V) = dim(W)$, quindi $dim(T(V)) = dim(W)$ \
  $=> T$ è anche suriettiva, quindi è biunivoca \
  Se $T$ è suriettiva, $T(V) = W => dim(W) = dim(V) = underbrace(dim(T(V)), = W) + dim(ker(T)) => dim(ker(T)) = 0 => ker(T) = {cal(O)_W} => T$ è anche iniettiva, quindi è biunivoca.
])

== Isomorfismi

Consideriamo l'applicazione lineare $T: V -> W$ e il sottospazio $U display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Allora abbiamo che $T: U -> T(U)$, dunque possiamo dire che $dim(U) = dim(T(U))$. \
Consideriamo ora la funzione lineare $L_A: KK^n -> KK^m$ associata alla matrice $A in MM_(m,n) (KK)$. Se essa è un isomorfismo, per il @apl:npr, $dim(KK^n) = dim(KK^m) <=> n = m$, quindi la matrice $A$ è quadrata. Inoltre, per il @apl:bfl, se $dim(KK^n) = dim(KK^m)$ allora $L_A$ è biunivoca $<=> L_A$ è iniettiva $<=> ker(L_A) = ker(A) = {cal(O)_V} <=> dim(ker(A)) = n - r k(A) = 0 <=> n = r k(A)$. Quindi abbiamo anche che $A$ è invertibile. Infatti possiamo verificare che $L_A^(-1) = L_(A^(-1))$. \
In generale, una funzione lineare è univocamente individuata dalle immagini di una sua base.

#theorem(
  title: [Teorema di interpolazione di funzioni lineari],
  [
    Siano $B = {v_1, ..., v_n}$ base di $V$ e $w_1, ..., w_n in W$ non necessariamente distinti. Allora esiste ed è unica la funzione $F: V -> W$ con $F(v_i) = w_i$ per $i = 1, ..., n$ definita $F(v) = display(sum^n_(i = 1)) c_i w_i$
  ],
)
#proof([
  Sia $F: V -> W display(<=>^"def.")F(h v_1 + k v_2) = display(sum^n_(i = 1)) d_i w_i, forall n, k in KK, forall v_1, v_2 in V$ dove \

  $vec(d_1, dots.v, d_n) = [h v_1 + k v_2]_B = h[v_1]_B + k[v_2]_B = h vec(a_1, dots.v, a_n) + k vec(b_1, dots.v, b_n)$, quindi $d_i = h a_i + k b_i$. Allora \

  $display(sum^n_(i = 1)) d_i w_i = display(sum^n_(i = 1)) (h a_i + k b_i)w_i = h display(sum^n_(i = 1)) underbrace(a_i, [v_1]_B) w_i + k display(sum^n_(i = 1)) underbrace(b_i, [v_2]_B) w_i = h F(v_1) + k F(v_2)$. Quindi $F$ è lineare e $F(v_i) = w_i$. Poiché $B$ base di $V$, $[v_i]_B = vec(c_1, dots.v, c_n) = e_i <=> v_i = 0 dot v_1 + ... + 1 dot v_i +$ \ $+ 0 dot v_(i + 1) + ... + 0 dot v_n$. Quindi $F(v_j) = display(sum^n_(i = 1)) c_i w_i = w_i$, in quanto $c_i = 1$ se $i = j$, altrimenti $0$.
])

#theorem(
  title: [Teorema di rappresentazione di funzioni lineari],
  [
    Sia $T: attach(V, tl: B) -> W^B'$ lineare con $B = {v_1, ..., v_n}$ e $B' = {w_1, ..., w_n}$. Allora la matrice \
    $A = ([T(v_1)]_B' | ... | [T(v_n)]_B')$ rappresenta T, ossia:
    1. $[T(v)]_B' = L_A ([v]_B) = A dot [v]_B, forall v in V$
    2. $[ker(T)]_B = ker(L_A) = ker(A)$, quindi $dim(ker(T)) = n - r k(A)$
    3. Se $U = cal(L)(u_1, ..., u_l) display(op(subset.eq, limits: #true)^(s.s.v.)) V$, allora $[T(U)]_B' = cal(L)(L_A ([u_1]_B), ..., L_A ([u_l]_B))$
    4. $[T(V)]_B' = cal(L)(C o l(A))$ quindi $dim(T(V)) = r k(A)$
  ],
)
#proof([
  1. $v = display(sum^n_(i = 1)) c_i v_i <=> [v]_B = vec(c_1, dots.v, c_n) => T(v) = T(display(sum^n_(i = 1)) c_i v_i) = display(sum^n_(i = 1)) c_i T(v_i)$. Considerando le coordinate, $[T(v)]_B' = [display(sum^n_(i = 1)) c_i T(v_i)] = display(sum^n_(i = 1)) c_i [T(v_i)]_B' = c_1 [T(v_1)]_B' + ... + c_n [T(v_n)]_B' = ([T(v_1)]_B' | ... | [T(v_n)]_B') dot vec(c_1, dots.v, c_n) = A dot [v]_B$
  2. $ker(T) = {v in V : T(v) = cal(O)_W}$ quindi $[cal(O)_W]_B' = [T(v)]_B' = A dot [v]_B <=> [ker(T)]_B = ker(A)$
  3. Sappiamo che $T(U) = cal(L)(T(u_1), ..., T(u_l))$ quindi $[T(U)]_B' = cal(L)([T(u_1)]_B', ..., [T(u_l)]_B') = cal(L)(A dot [u_1]_B, ..., A dot [u_l]_B)$ per l'isofmorfismo delle coordinate
  4. Applicando la 3. nel caso $U = V$ si ha $[T(V)]_B' = cal(L)(A dot [v_1]_B, ... A dot [v_n]_B)$
])

#theorem(
  title: [Matrice rappresentativa di composizione di funzioni lineari],
  [
    Siano $F: attach(V, tl: B) -> W^B'$ e $T: attach(W, tl: B') -> H^B''$. Allora $M_B^B'' (T compose F) = M_B'^B'' (T) dot M_B^B' (F)$
  ],
) <apl:mrc>
#corollary([
  Se $T: attach(V, tl: B) -> W^B'$ è un isomorfismo, allora $M_B'^B (T^(-1)) = (M_B^B'(T))^(-1)$. Quindi $T$ è un isomorfismo se e solo se $r k(M_B^B' (T)) = dim(V) = dim(W)$.
])
#proof([
  Sia $B = {v_1, ..., v_n}$. Poiché $T^(-1) compose T = I_V$, per il @apl:mrc, \
  $M_B^B (I_V) = M_B^B (T^(-1) compose T) = M_B'^B (T^(-1)) dot M_B^B' (T)$. Calcoliamo $M_B^B (I_V) = ([v_1]_B | ... | [v_n]_B) = (e_1 | ... | e_n) = I$, allora $I = M_B'^B (T^(-1)) dot M_B^B' (T)$. Quindi $M_B'^B (T^(-1)) = (M_B^B' (T))^(-1)$
])
#note-box([Se $T$ è un isomorfismo, $M_B^B' (T)$ è una matrice quadrata.])

== Cambi di base

#definition(
  title: [Matrice di cambio base],
  [
    La matrice $M_B^B' (I_V)$ che rappresenta $I_V: attach(V, tl: B) -> V^B'$ si dice _matrice di cambio base_ tra \
    $B = {v_1, ..., v_n}$ e $B' = {w_1, ..., w_n}$ e si calcola $M_B^B' (I_V) = ([v_1]_B' | ... | [v_n]_B')$.
  ],
)
Per calcolare tale matrice si applica Gauss-Jordan alla matrice $(w_1 | ... | w_n | v_1 | ... | v_n)$ così da ottenere la matrice $(I | [v_1]_B' | ... | [v_n]_B')$, ossia $(I | M_B^B' (I_V))$.
Se considero $I_V$ come un isomorfismo, allora abbiamo che $M_B'^B (I_V^(-1)) = (M_B^B' (I_V))^(-1)$ e, poiché $I^(-1) = I$, $M_B'^B (I_V) = (M_B^B' (I_V))^(-1)$.

Un'altra strategia prevede l'utilizzo di una "base ponte" intermedia $P$ più semplice, come la base canonica, per cui risulta facile calcolare $M_B^P (I)$ e $M_B'^P (I)$. Infatti, dal @apl:mrc, $M_B^B' (I) = M_P^B' (I) dot M_B^P (T) = (M_B'^P (I))^(-1) dot M_B^P (I)$.

#note-box([
  Un endomorfismo $T: attach(V, tl: B) -> V^B'$ ha una $M_B^B' (T) in MM_(n,n)(KK)$ con $n = dim(V)$. In generale, si tende ad utilizzare per comodità la stessa base, quindi $T: attach(V, tl: B) -> V^B$.
])
Questa strategia risulta utile per cambiare la base dell'endomorfismo: infatti, se consideriamo $T: attach(V, tl: B) -> V^B$, abbiamo che $M_B'^B' (T) = M_B^B' (I) dot M_B^B (T) dot M_B'^B (I)$, ossia, se $P = M_B'^B (I)$, $M_B'^B' (T) = P^(-1) dot M_B^B (T) dot P$.
#proposition(title: [Similitudine delle matrici rappresentative], [
  Due matrici rappresentative dello stesso endomorfismo sono simili.
])

#theorem(
  title: [Teorema di rappresentazione completo],
  [
    Siano $V, W$ due spazi vettoriali con rispettive basi $B$ e $B'$. Allora, la funzione $M_B^B' : L(V, W) -> MM_(m,n) (KK)$, la quale associa un'applicazione lineare alla sua matrice associata, è un isomorfismo. In particolare, abbiamo che, se $T, F in L(V, W)$, allora $M_B^B' (a T + b F) = a M_B^B' (T) + b M_B^B' (F)$.
  ],
)

= Determinante

Il determinante di una matrice si può considerare come il *volume con segno del parallelepipedo che ha per lati le righe della matrice*. Il suo calcolo è possibile solo con matrici quadrate.
#pagebreak()
#proposition(
  title: [Proprietà del determinante],
  [
    La funzione $det: RR^n times ... times RR^n -> RR$ soddisfa le seguenti proprietà:
    1. è lineare su ciascun componente, ossia è multilineare
    2. lo scambio di righe comporta un cambio di segno
    3. se una riga è combinazione lineare delle altre, $det(A) = 0$
    4. la 2ª mossa di Gauss in forma ristretta ($R_i -> R_i + b R_j, i != j$) non ne cambia il valore
    5. se la matrice è triangolare ed ha diagonale i valori $d_1, ..., d_n$, allora $det(A) = d_1 dot ... dot d_n$
  ],
) <det:prp>
#proof([
  2. Per la proprietà 3, $0 = det(R_1, R_2 + R_3, R_3 + R_2) = det(R_1, R_2, R_3 + R_2) +$ \ $+ det(R_1, R_3, R_3 + R_2) = det(R_1, R_2, R_3) + det(R_1, R_2, R_2) + det(R_1, R_3, R_3) +$ $+ det(R_1, R_3, R_2) = det(R_1, R_2, R_3) + 0 + 0 + det(R_1, R_3, R_2)$ \ $<=> det(R_1, R_2, R_3) = -det(R_1, R_3, R_2)$
  3. $det(R_1, a R_1, + b R_3, R_3) = a det(R_1, R_1, R_3) + b det(R_1, R_3, R_3) = 0 + 0 = 0$
  4. $det(..., R_i, R_j, ...) = det(..., R_i + b R_j, R_j) = det(..., R_i, R_j, ...) + b det(..., R_j, R_j, ...) = det(..., R_i, R_j, ...) + 0 = det(..., R_i, R_j, ...)$
])

Posso calcolare il determinante con l'algoritmo di Gauss, tenendo conto che la prima mossa cambia i segni e che la seconda in forma ristretta lascia invariato il valore. Ottengo la matrice a scala $S$ dalla matrice $A$, e ho che $det(A) = (-1)^l det(S)$, dove $l$ rappresenta il numero di scambi di riga effettuati.

#theorem(title: [Proprietà di una matrice quadrata], [
  Sia $A in MM_(n,n)(KK)$. Allora sono equivalenti:
  - $r k(A) = n$
  - $A$ è invertibile
  - $det(A) != 0$
])
#proof([
  $1. => 3.$: $det(A) = (-1)^l det(S)$, quindi $abs(det(A)) = abs(det(S)) = abs(d_1) dot ... dot abs(d_n)$. Quindi \ $r k(A) = r k(S) = n <=> d_i != 0$. Ho quindi $n$ pivot, allora $abs(d_1) dot ... dot abs(d_n) != 0 <=> det(A) != 0$.
])
#definition(
  title: [Minore],
  [
    Il _minore $i, j$ di A_, con $A in MM_(n,n)(RR)$, è la matrice $hat(A)_(i j) in MM_(n,n)(KK)$ ottenuta non considerando la riga $i$ e la colonna $j$.
  ],
)

#theorem(
  title: [Teorema di esistenza ed unicità della funzione determinante],
  [
    Esiste ed è unica la funzione $det: MM_(n,n) (RR) -> RR$ che soddisfa le proprietà già citate nella @det:prp. Inoltre, fissata una riga $i$, vale la formula $det(A) = display(sum^n_(j = 1)) (-1)^(i + j) a_(i j) dot det(hat(A)_(i j))$, detta _sviluppo di Laplace_.
  ],
)
#note-box([Lo sviluppo di Laplace ha un costo spropositato di $O(n!)$, quindi è preferibile calcolare il determinante induttivamente.])

#theorem(title: [Determinante di una trasposta], [
  $det(A) = det(A^t)$
])
#note-box([Da questo teorema ne segue che tutte le proprietà viste finora valgono anche per le colonne.])
#theorem(title: [Teorema di Binet], [
  Siano $A, B in MM_(n,n)(RR)$. Allora $det(A dot B) = det(A) dot det(B)$.
]) <det:bin>
Il determinante ha delle conseguenze interessanti:
- Se $A$ è invertibile $det(A^(-1)) = det^(-1) (A) = 1 / det(A)$. Infatti, poiché $I = A dot A^(-1)$, per il @det:bin, $det(I) = det(A) dot det(A^(-1)) = 1 <=> det(A^(-1)) = 1 / det(A)$
- Se $A tilde B$ allora $det(A) = det(B)$. Infatti, se $A tilde B$, esiste una matrice $P$ invertibile tale che $A = P^(-1) dot B dot P <=> det(A) = cancel(det(P^(-1))) dot det(B) dot cancel(det(P)) = det(B)$
- Con piccole matrici quadrate, è utile per calcolare il rango quando ho, per esempio, dei parametri
- Può essere utile per determinare il rango di matrici non quadrate

== Sottomatrici

#definition(
  title: [Sottomatrice quadrata],
  [
    Si dice _sottomatrice quadrata di ordine $p$ di $A$_ la matrice $A' in MM_(p,p) (RR)$ ottenuta da $A in MM_(n,n) (RR)$ considerando l'intersezione tra $p$ righe e $p$ colonne. Ad essa si possono orlare una riga e una colonna, ottenendo la matrice $A'' in MM_(p + 1, p + 1) (RR)$.
  ],
)
#theorem(
  title: [Teorema degli orlati],
  [
    Sia $A in MM_(m,n) (KK)$. Allora $r k(A) = p <=> exists A' in MM_(p, p) (RR)$ sottomatrice di $A :$ \ $det(A') != 0, det(A'') = 0, forall A'' in MM_(p + 1, p + 1) (RR)$.
  ],
)
#theorem(
  title: [Calcolo della matrice inversa con complementi algebrici],
  [
    Se $A in MM_(n,n) (KK)$ è invertibile, allora $A^(-1) = 1 / det(A) (c_(i j))$ dove $c_(i j) = (-1)^(i + j) det(hat(A)_(i j))$.
  ],
)

= Diagonalizzazione

#definition(
  title: [Endomorfismo diagonalizabile],
  [
    Sia $T: attach(V, tl: B) -> V^B$ un endomorfismo con base $B$. $T$ si dice _diagonalizzabile_ se $M_B^B (T) tilde M_B'^B' (T)$ e quest'ultima è diagonale, ossia della forma $mat(
      lambda_1, ..., 0; dots.v, dots.down, dots.v;
      0, ..., lambda_n
    )$ con $lambda_i in KK$.
  ],
)
Se consideriamo dunque l'endomorfismo $T: attach(V, tl: B) -> V^B$ e costruiamo la matrice $M_B'^B' (T) = mat(
  lambda_1, ..., 0; dots.v, dots.down, dots.v;
  0, ..., lambda_n
)$ con $B' = {u_1, ..., u_n}$ otteniamo $M_B'^B' (T) = ([T(u_1)]_B' | ... | [T(u_n)]_B')$, dove $[T(u_i)]_B' = (0, ..., 0, lambda_i, 0, ..., 0)$, quindi $T(u_i) = 0 u_1 + ... + lambda_i u_i + ... + 0 u_n = lambda_i u_i$.

#definition(
  title: [Autovalori e autovettori],
  [
    Un vettore $u in V$ con $u != cal(O)_V$ tale che $T(u) = lambda u$ per un certo $lambda in KK$ è detto _autovettore_ di $T$ relativo all'_autovalore_ $lambda$.
  ],
)
#note-box([
  Se $u$ è autovettore di $T$ rispetto a $lambda$, allora anche $c dot u, forall c in KK$ è ancora autovalore rispetto a $lambda$ in quanto $T(c dot u) = c T(u) = c dot lambda dot u = lambda (c dot u)$.
])

#theorem(
  title: [Primo criterio di diagonalizzazione],

  [
    Sia $T: V -> V$. Allora $T$ è diagonalizzabile se e solo se esiste una base $B'$ di $V$ fatta di autovettori.
  ],
) <dia:pcd>
#warning-box([
  Dal precedente teorema emerge che non tutti gli endormorfismi sono diagonalizzabili.
])

#definition(
  title: [Spettro e autospazio],
  [
    L'insieme $sigma(T) = {lambda_1, ..., lambda_l}$ di autovalori distinti è detto lo _spettro di $T$_. Ad ogni $lambda_i$ è associato l'insieme $V_lambda_i = {v in V : T(v) = lambda_i v_i}$ detto _autospazio dell'autovalore $lambda_i$_, composto da tutti gli autovettori di $T$ relativi a $lambda_i$.
  ],
)

#proposition(
  title: [Autospazio come sottospazio],
  [
    Sia $lambda in sigma(T)$. Allora $V_lambda display(op(subset.eq, limits: #true)^(s.s.v.)) V$.
  ],
)
#proof([
  $forall u_1, u_2 in V_lambda, forall c_1, c_2 in KK$ \
  $T(c_1 u_1 + c_2 u_2) = c_1 T(u_1) + c_2 T(u_2) = c_1 lambda u_1 + c_2 lambda u_2 = lambda (c_1 u_1 + c_2 u_2) => c_1 u_1 + c_2 u_2 in V_lambda$
])

#proposition(title: [Proprietà di un autospazio], [
  Sia $T: attach(V, tl: B) -> V^B$ con $A = M_B^B (T)$. Allora:
  1. $[V_lambda]_B = ker(A - lambda I), forall lambda in sigma(T)$
  2. $dim(V_lambda) = n - r k(A - lambda I)$
  3. $lambda in sigma(T) <=> det(A - x I) = 0$
]) <dia:pda>
#proof([Siano $lambda in sigma(T), u in V_lambda$.
  1. $T(u) = lambda u <=> [T(u)]_B = [lambda u]_B = lambda [u]_B <=> A dot [u]_B = lambda [u]_B <=> (A - lambda I) dot [u]_B = underline(0) <=>$ \ $[u]_B in ker(A - lambda I) <=> V_lambda = ker(A - lambda I)$
  2. $dim(V_lambda) = dim([V_lambda)_B]) = dim(ker(A - lambda I)) = n - r k(A - lambda I)$
  3. Se $lambda in sigma(T)$, allora $V_lambda != {cal(O)_V} <=> ker(A - lambda I) != {underline(0)} <=> r k(A - lambda I) < n <=> det(A - lambda I) = 0$ \ $<=> lambda$ soddisfa l'equazione $det(A - x I) = 0$
])
#definition(
  title: [Molteplicità geometrica],
  [
    Sia $lambda in sigma(T)$. $dim(V_lambda) = m_g (lambda)$ è detta _molteplicità geometrica dell'autovalore $lambda$_.
  ],
)

#proposition(title: [Lineare indipendenza di autovettori], [
  Siano $lambda_1, ..., lambda_k in sigma(T)$ distinti e $v_i in V_lambda_i$. Allora $v_1, ..., v_k$ sono linearmente indipendenti.
])

Poiché $lambda_1, ..., lambda_k$ sono distinti, concludiamo che $V_lambda_1 inter V_lambda_2 = {cal(O)_V}$, perché, se così non fosse, potremmo considerare un vettore $u != cal(O)_V$ tale che $u in V_lambda_1, u in V_lambda_2$ per esempio, e risulta ovvio che l'insieme ${v_1, v_2 } = {u, u}$ non è linearmente indipendente. Dunque, per il @ssl:cube, se \
$V_lambda_1 inter V_lambda_2 = {cal(O)_V}$, abbiamo che $B_V_lambda_1 union B_V_lambda_2$ è linearmente indipendente ed è base di $V_lambda_1 plus.circle V_lambda_2$.

  Per lo stesso ragionamento possiamo concludere anche che $(V_lambda_1 plus.circle V_lambda_2) inter V_lambda_3 = {cal(O)_V}$. Infatti, se così non fosse, avremmo un $u_3 != cal(O)_V$ tale che $u_3 in (V_lambda_1 plus.circle V_lambda_2) inter V_lambda_3 <=> u_3 = u_1 + u_2, u_1 in V_lambda_1,$ \ $u_2 in V_lambda_2 <=> u_1, u_2, u_3$ sono linearmente dipendenti, il che è un assurdo per la proposizione precedente. Sempre dal @ssl:cube, $B_V_lambda_1 union B_V_lambda_2 union B_V_lambda_3$ è linearmente indipendente ed è base di \
$(V_lambda_1 plus.circle V_lambda_2) plus.circle V_lambda_3$.

Questo ragionamento può essere iterato fino all'ultimo autospazio $V_lambda_k$, trovando il sottospazio
$ W = ((((V_lambda_1 plus.circle V_lambda_2) plus.circle V_lambda_3) plus.circle V_lambda_4) plus.circle ...) plus.circle V_lambda_k = V_lambda_1 plus.circle V_lambda_2 plus.circle ... plus.circle V_lambda_k $
che ha per base $B_V_lambda_1 union B_V_lambda_2 union ... union B_V_lambda_k = display(union.big^k_(i = 1)) B_V_lambda_i$.

#proposition(title: [Somma diretta di autospazi], [
  Sia $sigma(T) = {lambda_1, ..., lambda_l}$. Allora $W = V_lambda_1 plus.circle ... plus.circle V_lambda_l$ ha base $display(union.big^(l)_(i = 1)) B_V_lambda_i$ quindi $dim(W) = display(sum^(l)_(i = 1)) abs(B_V_lambda_i) = display(sum^l_(i = 1)) dim(V_lambda_i) = display(sum^l_(i = 1)) m_g (lambda_i)$.
]) <dia:sda>

#theorem(title: [Criterio geometrico di diagonalizzazione], [
  Siano $T: V -> V$ e $sigma(T) = {lambda_1, ..., lambda_l}$. Allora $T$ è diagonalizzabile se e solo se $V = V_lambda_1 plus.circle ... plus.circle V_lambda_l$ \
  o equivalentemente $dim(V) = display(sum^l_(i = 1)) m_g (lambda_i)$.
]) <dia:cgd>
#proof([
  Dal @dia:pcd, $T$ è diagonalizzabile se e solo se $V$ ha una base di autovettori. Quindi, per la @dia:sda, poiché $V = V_lambda_1 plus.circle ... plus.circle V_lambda_l$, allora $dim(V) = display(sum^l_(i = 1)) m_g (lambda_i)$.
])

== Polinomio caratteristico

L'equazione al punto 3. della @dia:pda è in realtà un polinomio, dunque possiede certe proprietà. In particolare, può avere radici o meno in base al campo in cui sto lavorando. Infatti, se abbiamo un certo $p(x) in KK [x]$, esso si può decomporre in fattori di grado $1$, ossia
$ p(x) = (lambda_1 - x)^m_1 dot (lambda_2 - x)^m_2 dot ... dot (lambda_l - x)^m_l dot q(x) $
dove $lambda_1, ..., lambda_l$ sono le radici distinte, $m_i$ rappresenta la *molteplicità algebrica della radice $lambda_i$* e $q(x)$ è un polinomio che non ha radici in $KK$. Inoltre $display(sum^l_(i = 1)) m_a (lambda_i) <= n$, ossia la somma delle molteplicità algebriche delle radici è minore o uguale al grado di $p(x)$.

#definition(title: [Traccia di una matrice], [
  Sia $A in MM_(n,n) (KK)$ con $A = (a_(i j))$. Si dice _traccia di $A$_ la somma dei valori sulla diagonale di $A$, ossia
  $ tr(A) = sum^n_(i = 1) a_(i i) $
])
#theorem(title: [Teorema del polinomio caratteristico], [
  Siano $(V, +, dot, KK)$ uno spazio vettoriale, $T: attach(V, tl: B) -> V^B$ un endomorfismo e $A = M_B^B (T) = (a_(i j))$ con $A in MM_(n,n) (KK)$. Allora:
  1. la funzione $p_A (x) = det(A - x I)$ è un polinomio di $x$ di grado $n$ della forma $ p_A (X) = (-1)^n x^n + (-1)^(n - 1) tr(A) x^(n - 1) + ... + (-1)^(n - k) C_k x^(n - k) + ... + det(A) $ dove $C_k$ rappresenta la somma dei minori principali di ordine $k$ della matrice $A$.
  2. $p_A (x)$ non dipende dalla base $B$, quindi se consideriamo un'altra base $B'$ di $V$ e prendiamo la matrice $C = M_B'^B' (T)$, abbiamo che $p_A (x) = p_B (x)$
  3. se $A$ è diagonale, assume allora la forma $p_A (x) = (lambda_1 - x)...(lambda_n - x)$
]) <dia:tpc>
#proof([
  2. Sia $B'$ una nuova base di $V$. Allora $M_B'^B' (T) = C$ e $A tilde C$, quindi $C = P^(-1) A P$ con $P = M_B'^B (I d)$. Dunque $p_B (x) = det(B - x I) = det(P^(-1) A P - x P^(-1) P) = det(P^(-1) (A - x I) P) = cancel(det(P^(-1))) dot det(A - x I) dot cancel(det(P)) = det(A - x I)$
])
#proposition(title: [Proprietà di un endomorfismo diagonalizzabile], [
  Sia $T: attach(V, tl: B) -> V^B$ un endomorfismo diagonalizzabile. Allora:
  - $p_T (x)$ ha $n$ radici con $n = dim(V) = display(sum^n_(i = 1)) m_a (lambda_i)$
  - se $B' = {u_1, ..., u_n}$ è base di $V$ fatta di autovettori tali che $T(u_i) = lambda_i u_i$, allora \ $M_B'^B' (T) = d i a g(lambda_1, ..., lambda_n)$
  - $det(M_B^B (T)) = lambda_1 dot ... dot lambda_n, tr(M_B^B (T)) = display(sum^n_(i = 1)) lambda_i$
]) <dia:ped>
#proof([
  Sia $A = M_B^B (T)$. Poiché $T$ è diagonalizzabile, $A tilde D$ dove $D = d i a g(lambda_1, ..., lambda_n)$. \
  Per il @dia:tpc, $p_T (x) = p_A (x) = p_D (x) = (lambda_1 - x)...(lambda_n - x)$, quindi $p_T (x)$ ha $n$ radici $lambda_1, ..., lambda_n$ contate con la loro molteplicità. Poiché $A tilde D$, $det(A) = det(D) = lambda_1 dot ... dot lambda_n$ e \
  $tr(A) = tr(D) = lambda_1 + ... + lambda_n$.
])

Abbiamo dunque visto che, date $A, B in MM_(n,n)(KK)$ tali che $A tilde B$, allora $p_A (x) = p_B (x) $ \ $= det(A - x I) = det(B - x I)$. Inoltre $det(A) = det(B), tr(A) = tr(B)$ e $p_A (x)$ e $p_B (x)$ hanno le stesse radici con la stessa molteplicità algebrica. Dunque possiamo dire che per ogni radice $lambda$ di $A$ e $B$, la molteplicità geometrica deve coincidere, ossia $dim(ker(A - lambda I)) = dim(ker(B - lambda I))$.

#warning-box([
  Queste condizioni sono solo necessarie e, in generale, non sufficienti per determinare $A display(tilde^?) B$.
])
In generale, possiamo dire che $A tilde B$ quando $A tilde D$ e $B tilde D$ con una matrice diagonale $D$.

#proposition(title: [Criterio di similitudine per matrici diagonalizzabili], [
  Siano $A, B in MM_ (n,n) (KK)$. Se $A$ e $B$ sono diagonalizzabili, allora $A tilde B <=> p_A (x) = p_B (x)$.
])
#theorem(title: [Disuguaglianza fondamentale delle molteplicità], [
  Sia $lambda in sigma(T)$. Allora $1 <= m_g (lambda) <= m_a (lambda)$.
]) <dia:dfm>
#note-box([
  $m_g (lambda) >= 1$ poiché, per definizione di autovalore, $V_lambda != {cal(O)_V}$, ossia il vettore nullo non è mai l'unica soluzione della relazione $T(u) = lambda u, u in V_lambda$, quindi $m_g (lambda) = dim(V_lambda) != 0 <=> dim(V_lambda) >= 1$.
])

== Secondo criterio di diagonalizzabilità

#definition(title: [Autovalore regolare], [
  Un autovalore $lambda in sigma(T)$ si dice _regolare_ se $m_g (lambda) = m_a (lambda)$.
])
#note-box([
  Se un autovalore $lambda$ ha $m_a (lambda) = 1$ allora è regolare, poiché $1 <= m_g (lambda) <= m_a (lambda)$ quindi \
  $m_a (lambda) = m_g (lambda) = 1$.
])
#theorem(title: [Secondo criterio di diagonalizzabilità], [
  Sia $T: V -> V$ con $dim(V) = n$ e $sigma(T) = {lambda_1, ..., lambda_l}$. Allora $T$ è diagonalizzabile se e solo se $display(sum^l_(i = 1)) m_a (lambda_i) = n$ e $forall lambda_i in sigma(T), m_a (lambda_i) = m_g (lambda_i)$.
])
#proof([
  Supponiamo che $m_g (lambda) = m_a (lambda), forall lambda in sigma(T)$ e che $n = display(sum^l_(i = 1)) m_g (lambda_i)$. Allora abbiamo che $display(sum^l_(i = 1)) m_a (lambda_i) = display(sum^l_(i = 1)) m_g (lambda_i) = n$. Per il @dia:cgd, $T$ è diagonalizzabile. \
  Supponiamo ora che $T$ sia diagonalizzabile. Allora abbiamo che, per la @dia:ped, $display(sum^l_(i = 1)) m_a (lambda_i) = n$. Supponiamo per assurdo che ogni $lambda in sigma(T)$ non sia regolare, ossia $m_a (lambda) != m_g (lambda)$. Per il @dia:dfm, $m_g (lambda) < m_a (lambda)$ e, per il @dia:cgd, poiché $T$ è diagonalizzabile, $n = display(sum^l_(i = 1)) m_g (lambda_i)$, quindi $n = display(sum^l_(i = 1)) m_g (lambda_i) < display(sum^l_(i = 1)) m_a (lambda_i) = n$, il che è un assurdo poiché $n = n$ e non $n < n$, quindi ogni $lambda in sigma(T)$ è regolare, ossia $m_a (lambda) = m_g (lambda)l, forall lambda in sigma(T)$.
])

#pagebreak()
Possiamo utilizzare un algoritmo per verificare che un endomorfismo $T: V -> V$ sia diagonalizzabile:
1. Si fissa una base $B$ e si costruisce la matrice rappresentativa $A = M_B^B (T)$
2. Si costruisce $p_T (x) = det(A - x I)$
3. Si calcola $sigma(T)$, il quale è composto dalle radici distinte di $p_T (x)$
4. Si calcola $m_a (lambda)$ per ogni radice $lambda$ e si verifica che $display(sum^l_(i = 1)) m_a (lambda_i) = n$. Se è vera la relazione, si calcola $m_g (lambda) = dim(V_lambda) = dim(ker(A - lambda I)) = n - r k(A - lambda I)$ e si verifica che $m_g (lambda) = m_a (lambda)$. Se entrambe le uguaglianze sono verificate per ogni $lambda in sigma(T)$, $T$ è diagonalizzabile, viceversa non lo è
5. Si calcola una base $B_V_lambda_i$ di ogni autospazio $V_lambda_i$, quindi, poiché $[V_lambda_i]_B = ker (A - lambda_i I)$, si risolve il sistema $(A - lambda_i I) dot v = 0$. Si considera dunque l'unione $display(union.big^l_(i = 1)) B_V_lambda_i = {[u_1]_B, ..., [u_n]_B}$ di tutte le basi trovate. Allora $B' = {u_1, ..., u_n}$ è la base di autovettori che diagonalizza $T$.
6. Si calcola la matrice di cambio base $M_B'^B (I d) = P = ([u_1]_B | ... | [u_n]_B)$, dove $B'$ è una base di autovettori, con la relazione $P^(-1) A P = M_B'^B' (T) = d i a g(lambda_1, ..., lambda_n)$.

#note-box([
  Se $T$ non è iniettiva, $ker(T) != {cal(O)_V} => 0 in sigma(T) <=> V_0 = {v in V : T(v) = 0 dot v = cal(O)_V} = ker(T)$. Inoltre $p_T (x) = x^s q(x)$ con $s = m_a (0) => s >= 1$. \
  Se $M_B^B (T) = (a_(i j))$ è una matrice triangolare (superiore o inferiore), i suoi autovalori risiedono sulla diagonale. Abbiamo infatti $p_T (x) = det(A - x I) = (a_11 - x)(a_22 - x)...(a_(n n) - x)$.
])

#pagebreak()
#outline(title: [Indice dei dimostrabili], target: figure
  .where(kind: "theorem")
  .or(figure.where(kind: "proposition"))
  .or(figure.where(kind: "lemma")))

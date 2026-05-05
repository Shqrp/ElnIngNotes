#import "@preview/theorion:0.4.1": *
#import "@preview/itemize:0.2.0" as el

#import cosmos.rainbow: *

#show: show-theorion
#show: el.default-enum-list

#set text(lang: "it")
#set par(justify: true)
#set page(numbering: "I", footer: [], header: context {
  if counter(page).display() != "I" {
    if calc.odd(counter(page).get().at(0)) {
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
  title: [Campo],
  [
    Sia $(KK, plus.o, times.o)$ una struttura. Essa si dice _campo_ se:
    - $plus.o$ e $times.o$ sono due operazioni binarie interne
    - $plus.o$ e $times.o$ soddisfano le proprietà commutativa, associativa e distributiva di $times.o$ su $plus.o$
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
    Sia $(KK, +, dot, 0, 1)$ un campo. $V$ si dice _spazio vettoriale_ sul campo $KK$ se:
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
  $c_1 v_1 + ... + c_n v_n = 0$ per qualche $c_i != 0$. Supponiamo $c_1 != 0$ \
  $=> v_1 + (c_1^(-1) c_2) v_2 + ... + (c_1^(-1) c_n) v_n = 0 => v_1 = -(c_1^(-1) c_2) v_2 - ... - (c_1^(-1) c_n)v_n in cal(L)(v_2, ..., v_n)$ \
  $=> v_1 = d_2 v_2 + ... + d_n v_n <=> d_2 v_2 + ... + d_n v_n - v_1 = cal(O) => {v_1, ..., v_n}$ linearmente dipendenti.
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
#note-box(
  [Ad ogni vettore corrisponde un vettore centrato nell'origine a lui equipollente. ($exists! O B' ~ A B, forall A B in RR^2$). Ogni punto appartenente alla retta/piano/spazio affine può essere individuato da un vettore centrato nell'origine.],
)

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
#note-box(
  [L'equazione parametrica di una retta non è unica in quanto il punto noto può variare.],
)
#definition(
  title: [Piano in $AA_3$],
  [
    $
      pi = {P : O P = vec(x, y, z) tilde.eq vec(x_0, y_0, z_0) + t vec(x_v, y_v, z_v) + s vec(x_u, y_u, z_u), v parallel.not u, forall t, s in RR}
    $
    dove ${v, u}$ è detta _base della giacitura del piano $pi$_.
  ],
)

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
  - _paralleli_ se i loro vettori normali sono paralleli
  - _incidenti_ se $pi_1 inter pi_2 != emptyset$
  Siano $pi, r in AA_3$ un piano e una retta. Essi sono tra loro.
  - _paralleli_ se il vettore direttore della retta e il vettore normale del piano sono perpendicolari
  - _incidenti_ se $pi inter r != emptyset$
])


== Equazioni cartesiane

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
I coefficienti $a, b, c, d$ hanno un significato geometrico. Infatti, supponendo $d = 0$ abbiamo che
$
  a x + b y + c z = 0 <=> vec(a, b, c) dot vec(x, y, z) = 0 => vec(a, b, c) perp vec(x, y, z)
$
Dunque il vettore $(a, b, c)$ rappresenta il *vettore normale* del piano, il quale è perpendicolare ad ogni vettore appartenente al piano.

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
Corrisponde esattamente al prodotto per uno scalare fra due vettori. Più precisamente, dati due vettori $v, u$
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

#pagebreak()

= Sistemi lineari

#proposition(
  title: [Soluzione di sistemi lineari],
  [
    Un sistema lineare $A dot x = b$, con $A = (C_1 | ... | C_n)$, ha soluzione se e solo se $b in cal(L)(C_1, ..., C_n)$
  ],
)
#proof(
  [$b in cal(L)(C_1, ..., C_n) <=> exists " " overline(x_1), ..., overline(x_n) in KK : b = overline(x_1) dot C_1 + ... + overline(x_n) dot C_n$. Quindi $vec(overline(x_1), ..., overline(x_n))$ \ risolve il sistema.],
)

L'insieme delle soluzioni del sistema lineare $A dot x = b$, con $A in MM_(m,n)(KK), b in MM_(m,1)(KK)$ si indica:
$ S o l(A, b) = {x in KK^n : A dot x = b} $
Se $b = underline(O)_m$ allora il sistema è detto *omogeneo*.
#definition(
  title: [Kernel di una matrice],
  [
    Sia $A in MM_(m,n)(KK)$. Allora $ker(A) = S o l(A, underline(0)_m)$, dove il $ker(A)$ è detto _nucleo di A_ o _kernel di A_.
  ],
)
#note-box([
  - $ker(A) != emptyset$. Infatti $A dot underline(0)_n = underline(0)_m$. Quindi $underline(0)_n in ker(A)$.
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
#corollary(title: [Numero di pivot di una matrice a scala], [
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
#proof(
  [Poiché abbiamo dimostrato che le mosse di Gauss non cambiano $S o l(A, b)$, è sufficiente dimostrare il teorema per una qualsiasi matrice a scala. \
    1. $(A|b) display(op(-->, limits: #true)^("Gauss")_("Jordan")) R = (A'|b') => "va notato che" r k(A) <= r k(A|b)$. Se indichiamo con $x$ l'ultimo pivot (il quale si trova nel vettore $b$), allora sappiamo che il sistema ha soluzione se e solo se $x = 0$, ossia $S o l(A, b) != emptyset <=> r k(A) = r k(A') = r k(A'|b') = r k(A|b)$
    2. Segue dal @ssl:ssl.
  ],
)
#corollary(title: [Struttura dell'insieme di soluzioni], [
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
#pagebreak()

#theorem(title: [Caratteristiche di una matrice invertibile], [
  Sia $A in MM_(n,n)(KK)$. Allora:
  1. $A$ è invertibile
  2. $A dot x = b$ ha un'unica soluzione
  3. $r k(A) = n$
  4. $exists "inversa destra" D$
  5. $exists "inversa sinistra" S$
]) <ssl:cmi>
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
#corollary(title: [Dimensione dello spazio delle righe di una matrice], [
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
#pagebreak()
#proof([
  Sia $U display(op(subset.eq, limits: #true)^(s.s.v.)) H$. Allora $u = display(sum^l_(i = 1)) a_i u_i, h = display(sum^m_(i = 1)) b_i h_i, w = display(sum^k_(i = 1))c_i w_i$. \
  $u + h + w = cal(O) <=> u + h = -w$. $u + h in H$ poiché $U subset.eq H$. Dunque $w in H inter W => w = display(sum^k_(i = 1)) d_i u_i$. \
  $=> display(sum^l_(i = 1)) (a_i + d_i)u_i + display(sum^m_(i = 1)) b_i h_i = cal(O)$. È una combinazione lineare di ${u_1, ..., u_l, h_(l + 1), ..., h_m} = B_H$. Dunque, devono essere linearmente indipendenti, il che é possibile solo con $b_i = 0$. \
  $=> display(sum^l_(i = 1)) a_i u_i + display(sum^k_(i = 1)) c_i w_i = cal(O)$. È una combinazione lineare di ${u_1, ..., u_l, w_(l + 1), ..., w_k} = B_W$. Dunque, sono linearmente indipendenti se $a_i = 0, c_i = 0 => B_H union B_W$ linearmente indipendenti.
])
#corollary(title: [Base della somma di sottospazi], [
  Se $H inter W = {cal(O)}$ e $B_H, B_W$ sono basi di $H$ e $W$ rispettivamente, allora $B_H union B_W$ sono linearmente indipendenti. In particolare $B_(H + W) = B_H union B_W$.
]) <ssl:cube>
#definition(
  title: [Somma diretta di due sottospazi],
  [
    Siano $H, W display(op(subset.eq, limits: #true)^(s.s.v.)) V$ con $H inter W = {cal(O)}$. Allora $H + W$ è anche detta _somma diretta di $H$ e $W$_ e si indica $H plus.o W$.
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
#pagebreak()

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
    4. $T^(-1)(H) = cal(L)(alpha_1, ..., alpha_l) plus.o ker(T)$, dove $H = cal(L)(h_1, ..., h_l) subset.eq W, alpha_i in T^(-1)(h_i)$. Infatti ${alpha_1, ..., alpha_l}$ sono linearmente indipendenti, poiché controimmagini di $H$, dunque possiamo anche dire che $T^(-1)(H)$ è un sottospazio vettoriale e una sua base è ${alpha_1, ..., alpha_l} union B_(ker(T))$
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
- $L_A^(-1)(H) = cal(L)(alpha_1, ..., alpha_l) plus.o ker(A)$ con $H = cal(L)(b_1, ..., b_l)$ e $alpha_i in L_A^(-1)(b_i)$
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
#corollary(title: [Dimensione del kernel di una matrice], [
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
) <apl:int>
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
#corollary(title: [Matrice della funzione inversa], [
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
#pagebreak()

= Determinante

Il determinante di una matrice si può considerare come il *volume con segno del parallelepipedo che ha per lati le righe della matrice*. Il suo calcolo è possibile solo con matrici quadrate.
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
#note-box(
  [Lo sviluppo di Laplace ha un costo spropositato di $O(n!)$, quindi è preferibile calcolare il determinante induttivamente.],
)

#theorem(title: [Determinante di una trasposta], [
  $det(A) = det(A^t)$
])
#note-box(
  [Da questo teorema ne segue che tutte le proprietà viste finora valgono anche per le colonne.],
)
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
#pagebreak()

= Diagonalizzazione

#definition(
  title: [Endomorfismo diagonalizzabile],
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
#pagebreak()

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
$V_lambda_1 inter V_lambda_2 = {cal(O)_V}$, abbiamo che $B_V_lambda_1 union B_V_lambda_2$ è linearmente indipendente ed è base di $V_lambda_1 plus.o V_lambda_2$.

Per lo stesso ragionamento possiamo concludere anche che $(V_lambda_1 plus.o V_lambda_2) inter V_lambda_3 = {cal(O)_V}$. Infatti, se così non fosse, avremmo un $u_3 != cal(O)_V$ tale che $u_3 in (V_lambda_1 plus.o V_lambda_2) inter V_lambda_3 <=> u_3 = u_1 + u_2, u_1 in V_lambda_1,$ \ $u_2 in V_lambda_2 <=> u_1, u_2, u_3$ sono linearmente dipendenti, il che è un assurdo per la proposizione precedente. Sempre dal @ssl:cube, $B_V_lambda_1 union B_V_lambda_2 union B_V_lambda_3$ è linearmente indipendente ed è base di \
$(V_lambda_1 plus.o V_lambda_2) plus.o V_lambda_3$.

Questo ragionamento può essere iterato fino all'ultimo autospazio $V_lambda_k$, trovando il sottospazio
$
  W = ((((V_lambda_1 plus.o V_lambda_2) plus.o V_lambda_3) plus.o V_lambda_4) plus.o ...) plus.o V_lambda_k = V_lambda_1 plus.o V_lambda_2 plus.o ... plus.o V_lambda_k
$
che ha per base $B_V_lambda_1 union B_V_lambda_2 union ... union B_V_lambda_k = display(union.big^k_(i = 1)) B_V_lambda_i$.

#proposition(title: [Somma diretta di autospazi], [
  Sia $sigma(T) = {lambda_1, ..., lambda_l}$. Allora $W = V_lambda_1 plus.o ... plus.o V_lambda_l$ ha base $display(union.big^(l)_(i = 1)) B_V_lambda_i$ quindi $dim(W) = display(sum^(l)_(i = 1)) abs(B_V_lambda_i) = display(sum^l_(i = 1)) dim(V_lambda_i) = display(sum^l_(i = 1)) m_g (lambda_i)$.
]) <dia:sda>

#theorem(title: [Criterio geometrico di diagonalizzazione], [
  Siano $T: V -> V$ e $sigma(T) = {lambda_1, ..., lambda_l}$. Allora $T$ è diagonalizzabile se e solo se $V = V_lambda_1 plus.o ... plus.o V_lambda_l$ \
  o equivalentemente $dim(V) = display(sum^l_(i = 1)) m_g (lambda_i)$.
]) <dia:cgd>
#proof([
  Dal @dia:pcd, $T$ è diagonalizzabile se e solo se $V$ ha una base di autovettori. Quindi, per la @dia:sda, poiché $V = V_lambda_1 plus.o ... plus.o V_lambda_l$, allora $dim(V) = display(sum^l_(i = 1)) m_g (lambda_i)$.
])

== Polinomio caratteristico

L'equazione al punto 3. della @dia:pda è in realtà un polinomio, dunque possiede certe proprietà. In particolare, può avere radici o meno in base al campo in cui sto lavorando. Infatti, se abbiamo un certo $p(x) in KK [x]$, esso si può decomporre in fattori di grado $1$, ossia
$
  p(x) = (lambda_1 - x)^m_1 dot (lambda_2 - x)^m_2 dot ... dot (lambda_l - x)^m_l dot q(x)
$
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
#pagebreak()
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

Abbiamo dunque visto che, date $A, B in MM_(n,n)(KK)$ tali che $A tilde B$, allora $p_A (x) = p_B (x)$ \ $= det(A - x I) = det(B - x I)$. Inoltre $det(A) = det(B), tr(A) = tr(B)$ e $p_A (x)$ e $p_B (x)$ hanno le stesse radici con la stessa molteplicità algebrica. Dunque possiamo dire che per ogni radice $lambda$ di $A$ e $B$, la molteplicità geometrica deve coincidere, ossia $dim(ker(A - lambda I)) = dim(ker(B - lambda I))$.

#warning-box([
  Queste condizioni sono solo necessarie e, in generale, non sufficienti per determinare $A display(tilde^?) B$.
])
In generale, possiamo dire che $A tilde B$ quando $A tilde D$ e $B tilde D$ con una matrice diagonale $D$.

#proposition(title: [Criterio di similitudine per matrici diagonalizzabili], [
  Siano $A, B in MM_(n,n) (KK)$. Se $A$ e $B$ sono diagonalizzabili, allora $A tilde B <=> p_A (x) = p_B (x)$.
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

= Spazi euclidei

#let pscal(u, v) = [$chevron.l$ #u$,$ #v $chevron.r$]
#let ppscal(u, v) = [$chevron.l chevron.l$ #u$,$ #v $chevron.r chevron.r$]

#definition(title: [Prodotto scalare], [
  Sia $(V, +, dot, RR)$ uno spazio vettoriale. Allora $pscal(dot, dot): V times V -> RR$ è una funzione detta _prodotto scalare_ che associa due vettori $u, v in V$ al numero $pscal(u, v) in RR$ e possiede le seguenti proprietà:
  - bilinearità: $pscal(v + w, u) = pscal(u, w) + pscal(v, w), pscal(c dot v, u) = c dot pscal(v, u) = pscal(v, c dot u), forall v, u, w in V, forall c in KK$
  - simmetria: $pscal(v, u) = pscal(u, v), forall u, v in V$
  - è definita positiva: $pscal(v, v) >= 0, forall v in V$ e $pscal(v, v) = 0 <=> v = cal(O)_V$
])
#definition(title: [Spazio euclideo], [
  Lo spazio vettoriale arricchito del prodotto scalare $(V, +, dot, RR, pscal(dot, dot))$ è detto _spazio euclideo_.
])
#note-box([
  Per bilinearità, le sommatorie si possono portare dentro e fuori, ossia $pscal(v, sum a_i u_i) = sum a_i pscal(v, u_i)$.
])

Dato uno spazio vettoriale che è anche euclideo si possono definire:
- la *norma* di un vettore: $norm(v) = sqrt(pscal(v, v)), forall v in V$ quindi $norm(v) = 0 <=> v = cal(O)_V$
- la *distanza* tra due vettori: $d(v, u) = norm(v - u), forall v, u in V$

La norma possiede le seguenti proprietà:
- *omogeneità*: $norm(c dot v) = abs(c) dot norm(v), forall c in KK, forall v in V$ \
  _Dimostrazione_: $norm(c dot v)^2 = pscal(c dot v, c dot v) = c^2 pscal(v, v) = c^2 norm(v)^2 <=> norm(c dot v) = abs(c) dot norm(v)$
- *teorema di Carnot*: $norm(v plus.minus u)^2 = norm(v)^2 plus.minus 2 pscal(v, u) + norm(u)^2$ \
  _Dimostrazione_: Siano $u, v in V, t in RR$. Allora $norm(u + t v)^2 = pscal(u + t v, u + t v) = pscal(u, u + t v) +$ \ $t pscal(v, u + t v) = pscal(u, u) + t pscal(u, v) + t pscal(v, u) + t^2 pscal(v, v) = norm(u)^2 + 2t pscal(u, v) + t^2 norm(v)^2$
- *disuguaglianza di Cauchy-Schwarz*: $abs(pscal(v, u)) <= norm(v) dot norm(u)$ \
  _Dimostrazione_: Considerando la relazione precedente come un polinomio in $t$ abbiamo che \ $t^2 norm(v)^2 + 2t pscal(v, u) + norm(u)^2 >= 0, forall t in RR$ poiché $norm(u + t v) >= 0$, quindi il polinomio non deve avere radici oppure ne deve avere una sola, ossia $b^2 - 4a c <= 0 <=> 4 pscal(v, u)^2 <= 4 norm(v)^2 norm(u)^2 <=> abs(pscal(v, u)) <= norm(v) dot norm(u)$
- *disuguaglianza triangolare*: $norm(v + u) <= norm(v) + norm(u)$

#definition(title: [Angolo tra vettori], [
  $forall v, u in V, cos theta = pscal(v, u) / (norm(v) dot norm(u)) <=> theta = arccos pscal(v, u) / (norm(v) dot norm(u)) in [0, 2pi]$.
])
#note-box([
  Da Cauchy-Schwarz, abbiamo che $-(norm(v) dot norm(u)) <= pscal(v, u) <= norm(v) dot norm(u) <=> -1 <= pscal(v, u) / (norm(v) dot norm(u)) <= 1$, infatti $-1 <= cos theta <= 1, forall theta in [0, 2pi]$.
])

Da questa definizione emerge che il prodotto scalare è nullo quando $u$ e $v$ sono ortogonali tra loro. Infatti $u perp v <=> theta = pi / 2 <=> cos pi/2 = 0$. Quindi, dal teorema di Carnot abbiamo anche il teorema di Pitagora, ossia, con $u perp v$, $norm(u - v)^2 = norm(u)^2 - underbrace(pscal(u, v), = 0) + norm(v)^2 = norm(u)^2 + norm(v)^2$.

#proposition(title: [Proprietà del prodotto scalare generalizzato], [
  Siano $A in MM_(n,n) (RR), x, y in RR^n$. Allora:
  1. $pscal(x, y) = x^t A y$ è bilineare
  2. Se $A$ è simmetrica, allora lo è anche $pscal(x, y) = x^t A y$
  3. $pscal(x, y) = x^t A y = display(sum_(i, j = 1)^n) x_i a_(i j) y_j$ con $x = vec(x_1, dots.v, x_n), y = vec(y_1, dots.v, y_n)$
])
#proof([
  1. Sia $z in RR^n$. Allora $pscal(c_1 x + c_2 z, y) = (c_1 x + c_2 z)^t A y = (c_1 x^t + c_2 z^t) A y = c_1 x^t A y + c_2 z^t A y = c_1 pscal(x, y) + c_2 pscal(z, y)$
  2. Poiché $c = (c)^t, forall c in RR$, $pscal(x, y) = x^t A y = (x^t A y)^t = y^t (x^t A)^t = y^t A^t x = y^t A x = pscal(y, x)$
])

== Matrice di Gram

#definition(title: [Matrice di Gram], [
  Sia $(V, +, dot, RR, pscal(dot, dot))$ euclideo con $B = {v_1, ..., v_n}$ base di $V$. Allora si dice _matrice di Gram_ rispetto alla base $B$ la matrice $S_B in MM_(n,n) (RR)$ tale che $(S_B)_(i j) = pscal(v_i, v_j)$.
])
#proposition(title: [Prodotto scalare con la matrice di Gram], [
  Siano $u, w in V$ e $B = {v_1, ..., v_n}$ base di $V$. Allora $pscal(u, w) = [u]_B^t S_B [w]_B^t$.
])
#proof([
  $u = display(sum_(i = 1)^n) a_i v_i, [u]_B = vec(a_1, dots.v, a_n), w = display(sum_(j = 1)^n) b_j v_j, [w]_B = vec(b_1, dots.v, b_n)$. Allora $pscal(u, w) = pscal(display(sum_(i = 1)^n) a_i v_i, display(sum_(i = 1)^b) b_j v_j) = display(sum_(i, j = 1)^n) a_i b_j pscal(v_i, v_j) = display(sum_(i, j = 1)^n) a_i b_j (S_B)_(i j) = (a_1, ..., a_n) S_B vec(b_1, dots.v, b_n) = [u]_B^t S_B [w]_B$.
])

#note-box([
  La matrice di Gram permette di passare da uno spazio euclideo astratto $(V, +, dot, RR, pscal(dot, dot))$ a quello delle coordinate $(R^n, +, dot, RR, ppscal(dot, dot))$ utilizzando $pscal(u, w) = [u]_B^t S_B [w]_B$. Infatti questa è una funzione bilineare, simmetria e definita positiva di $RR^n$.
])

== Ortogonalità

#definition(title: [Vettori ortogonali e ortonormali], [
  Siano $(V, +, dot, RR, pscal(dot, dot))$ euclideo e ${v_1, ... , v_k}$ un insieme di vettori. Allora $v_i != v_j$ si dicono:
  - _ortogonali_ ($perp$) se $pscal(v_i, v_j) = 0$
  - _ortonormali_ ($o.n.$) se $v_i perp v_j$ e $norm(v_i) = norm(v_j) = 1 <=> pscal(v_i, v_i) = 0, pscal(v_j, v_j) = 0$
])
#note-box([
  Se ${b_1, ..., b_n}$ sono $o.n.$, allora $pscal(b_i, b_j) = cases(1 &"se" i = j, 0 &"se" i = j) = delta_(i j)$. Inoltre, se ${a_1, ..., a_k}$ sono $perp$ e $c_i = a_i / norm(a_i)$ allora ${c_1, ..., c_k}$ sono $o.n.$
])

#proposition(title: [Coefficienti di Fourier], [
  Siano $(V, +, dot, RR, pscal(dot, dot))$ euclideo, ${b_1, ..., b_l} perp$ e $[v]_B = vec(a_1, dots.v, a_l)$. Allora $a_i = pscal(v, b_i) / norm(b_i)^2$ e, se ${b_1, ..., b_k} " " o.n.$, allora $a_i = pscal(v, b_i)$. Inoltre ${b_i, ... b_l}$ sono linearmente indipendenti, poiché $perp$.
])
#proof([
  Fissato un certo $b_i$, $pscal(v, b_i) = pscal(display(sum_(j = 1)^l) a_j b_j, b_i) = display(sum_(j = 1)^l) a_j pscal(b_j, b_i)$. Se $i != j$, $pscal(b_j, b_i) = 0$ poiché $b_j perp b_i$ se $i != j$. Invece, se $i = j$, $a_i pscal(b_j, b_i) = a_i norm(b_i)^2 <=> a_i = pscal(v, b_i) / norm(b_i)^2$.
])

#corollary(title: [Coordinate rispetto a una base ortogonale o ortonormale], [
  Se $B = {b_1, ..., b_n}$ è base $perp$ di $V$, allora $[v]_B = vec(pscal(v, b_1) / norm(b_1)^2, dots.v, pscal(v, b_n) / norm(b_n)^2)$. Se $B$ è $o.n.$, allora $[v]_B = vec(pscal(v, b_1), dots.v, pscal(v, b_n))$.
])

#note-box([
  Se abbiamo $n = dim(V)$ vettori $perp$, allora essi sono una base $perp$ di $V$.
])
#corollary(title: [Matrice di Gram di una base ortonormale], [
  Se $B = {b_1, ..., b_n}$ è base $o.n.$ di $V$, allora $S_B = I$.
]) <spe:mbo>
#proof([
  $(S_B)_(i j) = pscal(b_i, b_j) = cases(0 &"se" i != j, 1 &"se" i = j) = delta_(i j) => S_B = I$.
])

Quindi abbiamo che $pscal(u, v) = [u]_B^t I [v]_B = [u]_B^t [v]_B$ se abbiamo una base ortonormale. In altre parole, passando alle coordinate rispetto a una base ortonormale, il prodotto scalare tra due vettori si riduce al prodotto scalare standard delle loro coordinate.

#definition(title: [Complemento ortogonale], [
  Sia $W display(op(subset.eq, limits: #true)^(s.s.v.)) V$ con $(V, +, dot, RR pscal(dot, dot))$ euclideo. Allora l'insieme $W^perp := {v in V : pscal(v, w) = 0, forall w in W}$ è detto _complemento ortogonale di $W$_.
])
#proposition(title: [Proprietà del complemento ortogonale], [
  1. $W^perp display(op(subset.eq, limits: #true)^(s.s.v.)) V$
  2. Se ${w_1, ..., w_m}$ è base di $W$, allora $v in W^perp <=> pscal(v, w_i) = 0$ con $i = 1, ..., m$
  3. $(W^perp)^perp = W$
  4. $V = W plus.o W^perp$
]) <spe:pco>
#proof([
  1. Per la @ssl:csv, $forall u_1, u_2 in W^perp, forall w in W, forall c_1, c_2 in RR$ \ $pscal(c_1 u_1 + c_2 u_2, w) = c_1 pscal(u_1, w) + c_2 pscal(u_2, w) = 0 + 0 = 0 => c_1 u_1 + c_2 u_2 in W^perp$
  2. $pscal(v, w) = pscal(v, display(sum_(i = 1)^m) a_i w_i) = display(sum_(i = 1)^m) a_i pscal(v, w_i) = 0 => v in W^perp$
  4. Sia $v in W inter W^perp <=> v in W, v in W^perp$. Allora $pscal(v, v) = 0$, poiché $W perp W^perp$ e $pscal(v, v) = norm(v)^2$, quindi $norm(v)^2 = 0 <=> v = cal(O)_V$
])

=== Proiezione ortogonale

#definition(title: [Proiezione ortogonale su un sottospazio], [
  Sia $W display(op(subset.eq, limits: #true)^(s.s.v.)) V$. Si dice _proiezione ortogonale su $W$_ l'endomorfismo $P_W: V -> V$ tale che:
  1. $P_W (V) = W$
  2. $P_W (w) = w, forall w in W$ o, equivalentemente, $P_W compose P_W = P_W$
  3. $v - P_W (v) in W^perp, forall v in V$
]) <spe:pos>
Infatti possiamo dire che ogni vettore $v$ di $V$ si può scrivere come
$ v = underbrace(P_W (v), in W) + underbrace((v - P_W (v)), in W^perp) $
considerando $P_W (v)$ come la "componente orizzontale" di $v$ e $v - P_W (v)$ la "componente verticale".

#theorem(title: [Esistenza, unicità e formula della proiezione ortogonale], [
  Siano $(V, +, dot, RR, pscal(dot, dot))$ uno spazio euclideo, $W = cal(L) (b_1, ..., b_m)$ dove ${b_1, ..., b_m}$ è una base $o.n.$ di $W$. Allora la funzione $P_W: V -> V$ definita da $P_W (v) = display(sum_(i = 1)^m pscal(v, b_i) dot b_i)$ è l'unico endomorfismo che soddisfa tutte le proprietà nella @spe:pos. Inoltre $P_(W^perp) (v) = v - P_W (v), forall v in V$
])
#proof([
  Dimostriamo le proprietà definite nella @spe:pos.
  2. Fissato $b_i$, $P_W (b_i) = display(sum_(j = 1)^m) pscal(b_i, b_j) dot b_j = 0 + ... + underbrace(norm(b_i)^2 dot b_i, i = j) = b_i$ poiché $b_i " " o.n.$ Allora \ $forall w in W, w = display(sum_(k = 1)^m) c_k b_k => P_W (w) = P_W (display(sum_(k = 1)^m) c_k b_k) = display(sum_(k = 1)^m) c_k P_W (b_k) = display(sum_(k = 1)^m) c_k b_k = w$
  1. $P_W (v) = display(sum_(j = 1)^m) pscal(v, b_j) dot b_j in W, forall v in V => P_W (V) subset.eq W$. Inoltre, per il punto 2, $P_W (V) = W$.
  3. $v - P_W (v) in W^perp <=> pscal(v - P_W (v), b_i) = 0, forall i = 1, ..., m$. Allora $pscal(v - P_W (v), b_i) =$ \  $= pscal(v - display(sum_(j = 1)^m) pscal(v, b_j) dot b_j, b_i) = pscal(v, b_i) - underbrace(display(sum_(j = 1)^m) pscal(v, b_j), = pscal(v, b_i)) dot underbrace(pscal(b_j, b_i), = delta_(j i)) = pscal(v, b_i) - pscal(v, b_i) = 0$ \
  L'unicità segue dal @apl:int, verificando che $P_(W^perp) = I d - P_W$.
])

#theorem(title: [Generazione di una base ortonormale con Gram-Schmidt], [
  Siano $(V, +, dot, RR, pscal(dot, dot))$ euclideo, $W = cal(L) (w_1, ..., w_m)$ con $w_1, ..., w_m$ linearmente indipendenti. Allora posso generare una base $o.n.$ di $W$ con l'algoritmo di Gram-Schmidt.
])

Dati i vettori linearmente indipendenti ${w_1, ..., w_m}$, l'algoritmo procede nel seguente modo:
1. $b_1 = w_1 / norm(w_1)$
2. $b_2 = u_2 / norm(u_2)$ dove $U_1 = cal(L) (b_1)$ e $u_2 = P_U_1^perp (w_2) = w_2 - P_(U_1) (w_2) = w_2 - (pscal(w_2, b_1) dot b_1) => b_1 perp b_2$
3. $b_3 = u_3 / norm(u_3)$ dove $U_2 = cal(L) (b_1, b_2)$ e $u_3 = P_U_2^perp (w_3) = w_3 - P_U_2 (w_3) =$ \ $= w_3 - (pscal(w_3, b_1) dot b_1 + pscal(w_3, b_2) dot b_2) => b_1 perp b_2 perp b_3$
$dots.v$ \
#enum(numbering: "a.", enum.item(13)[
  $b_m = u_m / norm(u_m)$ dove $U_(m - 1) = cal(L) (b_1, ..., b_(m - 1))$ e $u_k = P_U_(m - 1)^perp (w_m) = w_m - P_U_(m - 1) (w_m) =$ \  $= w_m - (display(sum_(j = 1)^(m - 1)) pscal(w_m, b_j) dot b_j) => b_1 perp ... perp b_m$
])
Otteniamo così un insieme di vettori ${b_1, ..., b_m} " " o.n.$, il quale è una base $o.n.$ di $W$.

#theorem(title: [Ulteriori proprietà della proiezione ortogonale], [
  Siano $P_W: attach(V, tl: B) -> V^B$, $W = cal(L) (b_1, ..., b_m)$ e $B' = {b_1, ..., b_m}$ una base $o.n.$ di $W$. Allora:
  1. $ker(P_W) = W^perp$
  2. $norm(v - w) > norm(v - P_W (v)), forall w in W, w != P_W (v)$, ossia $P_W (v)$ è il vettore di $W$ più vicino a $v$
  3. $M_B^B (P_W) = display(sum_(i = 1)^m) [b_i]_B dot [b_i]^t dot S_B$, dove $B$ è la base di $V$
  4. $M_B^B (P_(W^perp)) = M_B^B (I d - P_W) = I - M_B^B (P_W)$
])

#proof([
  1. Sia $v in ker(P_W)$. Allora $cal(O)_V = P_W (v) = display(sum_(i = 1)^m) pscal(v, b_i) dot b_i$. Poiché ogni $b_i$ è linearmente indipendente, questa domma fa $0$ se e solo se ogni coefficiente è $0 <=> pscal(v, b_i) = 0 <=> v in W^perp <=> ker(P_W) = W^perp$
  2. Siano $u_1 = v - P_W (v) in W^perp, u_2 = v - w, u_3 = w - P_W (v) != cal(O)_V$. Poiché $u_1 perp u_3$ e $u_2 = u_1 + u_3$, da Pitagora, $norm(u_2)^2 = norm(u_1)^2 + norm(u_3)^2 > norm(u_1)^2 <=> norm(u_2)^2 > norm(u_1)^2 <=> norm(v - w) > norm(v - P_W (v))$
  3. $M_B^B (P_W) dot [v]_B = display(sum_(i = 1)^m) [b_i]_B dot underbrace([b_i]_B^t dot S_B dot [v]_B, pscal(b_i, v)) = display(sum_(i = 1)^m) [b_i]_B pscal(b_i, v) = [display(sum_(i = 1)^m) pscal(b_i, v) b_i]_B = [P_W (v)]_B$
])
#note-box([
  $P_W (v)$ è il vettore di $W$ che meglio approssima $v$. Inoltre, per il @spe:mbo, se $B$ è base $o.n.$ di $V$, allora $S_B = I$, quindi $M_B^B (P_W) = display(sum_(i = 1)^m) [b_i]_B dot [b_i]_B^t$
])

== Trasformazioni affini

#definition(title: [Distanza tra sottospazi affini], [
  Siano $(V, +, dot, RR, pscal(dot, dot))$ uno spazio euclideo, $A_1$ e $A_2$ sottospazi affini. Allora si dice _distanza tra $A_1$ e $A_2$_ il valore $d(A_1, A_2) = min {d(P_1, P_2) = norm(P_1 - P_2) : P_1 in A_1, P_2 in A_2}$.
])
#theorem(title: [Distanza tra sottospazi affini come proiezione], [
  Siano $A_1 = P_1 + W_1$ e $A_2 = P_2 + W_2$ due sottospazi affini. Allora $d(A_1, A_2) = norm(P_(U^perp) (P_1 - P_2))$, dove $U = W_1 + W_2$.
])
#definition(title: [Trasformazione affine], [
  Sia $(V, +, dot, RR)$ uno spazio vettoriale. Si dice _trasformazione affine_ la funzione $f: V -> V$ tale che $f(v) = v_0 + T(V)$ dove $v_0 in V$ e $T: V -> V$ è un endomorfismo.
])
Abbiamo dunque che una trasformazione affine è la composizione di un endomorfismo con una traslazione, ossia:
$ tau_v_0 (x) = x + v_0 => f(x) = (tau_v_0 compose T)(x) = T(x) + v_0 $
#pagebreak()
Quindi una trasformazione affine manda un sottospazio affine in un altro sottospazio affine, ossia
$
  f(P_0 + W_1) = v_0 + T(P_0 + W_1) = underbrace(v_0 + T(P_0), v'_0) + underbrace(T(W_1), W'_1) = v'_0 + W'_1 "dove" W_1, W'_1 display(op(subset.eq, limits: #true)^(s.s.v.)) V
$

In generale, una trasformazione affine in uno spazio euclideo non preserva la metrica, però, se $T$ è un isomorfismo, quindi invertibile, $f$ preserva la dimensione del sottospazio affine: quindi, per esempio, un punto viene mandato in un punto, una retta in una retta e un piano in un piano.

== Isometrie

#definition(title: [Isometria lineare], [
  Un endomorfismo $T: V -> V$ si dice _isometria lineare_ se $pscal(T(v), T(u)) = pscal(v, u), forall v, u in V$.
])
#proposition(title: [Proprietà di un'isometria lineare], [
  Sia $T: V -> V$ un'isometria lineare. Allora:
  1. le norme si preservano, ossia $norm(T(v)) = norm(v), forall v in V$
  2. $T$ è un isomorfismo, quindi è sempre iniettiva
  3. gli angoli si preservano, ossia $cos theta = pscal(v, u) / (norm(v) dot norm(u)) = pscal(T(v), T(u)) / (norm(T(v)) dot norm(T(u)))$
])
#proof([
  1. $norm(T(v))^2 = pscal(T(v), T(v))$ quindi, per definizione, $= pscal(v, v) = norm(v)^2$
  2. Sia $v in ker(T)$. Allora $0 = norm(cal(O)_V) = norm(T(v)) = norm(v)$, quindi $v = cal(O)_V => ker(T) = {cal(O)_V}$
])
#theorem(title: [Caratterizzazione di un'isometria lineare], [
  Sia $T: attach(V, tl: B) -> V^B'$ con $B = {b_1, ..., b_n}$ e $B' = {b'_1, ..., b'_n}$ basi $o.n.$ di $V$. Allora $T$ è un'isometria lineare se e solo se $M_B^B' (T) = (C_1 | ... | C_n)$ dove $C_i^t dot C_j = delta_(i j)$, ossia se e solo se le colonne di $M_B^B' (T)$ sono una base $o.n.$ di $RR^n$ rispetto al prodotto scalare standard.
])
#proof([
  Se $B'$ è  $o.n.$, $S_B' = I$, quindi $pscal(u, v) = [u]_B'^t dot S_B dot [v]_B' = [u]_B'^t dot [v]_B'$. Poiché $M_B^B' (T) = ([T(b_1)]_B' | ... | [T(b_n)]_B')$, allora $C_i^t dot C_j = [T(b_i)]_B'^t dot [T(b_j)]_B' = pscal(T(b_i), T(b_j))$. Poiché $T$ è un'isometria lineare, $pscal(T(b_i), T(b_j)) = pscal(b_i, b_j)$, e, poiché $B$ è $o.n.$, $pscal(b_i, b_j) = delta_(i j)$.
])
#definition(title: [Matrice ortogonale], [
  Sia $A in MM_(n,n) (RR)$. Se $C o l(A)$ è una base $o.n.$ di $RR^n$, allora $A$ si dice _ortogonale_, quindi $A in O(n)$.
])
Quindi riconosco un'isometria lineare verificando che la sua matrice rappresentativa sia ortogonale.
#proposition(title: [Struttura di una matrice ortogonale], [
  Sia $A in O(n)$. Allora sono equivalenti:
  1. $C o l(A)$ è base $o.n.$ di $RR^n$
  2. $R i g(A)$ è base $o.n.$ di $RR^n$
  3. $A$ è invertibile e $A dot A^t = A^t dot A = I => A^t = A^(-1)$
])
#pagebreak()
#proof([
  - $1. => 3.$: $A = (C_1 | ... | C_n) <=> (A^t dot A)_(i j) = (vec(C_1^t, dots.v, C_n^t) dot (C_1 | ... | C_n))_(i j) = C_i^t dot C_j = delta_(i j)$ poiché \ #"             " $C o l(A)$ è $o.n.$ per ipotesi. Quindi $A dot A^t = I <=> A^t = A^(-1)$ per il @ssl:cmi.
  - $3. => 2.$: $A = vec(R_1, dots.v, R_n)$ e $A dot A^t = I$ quindi $R_i dot R_j^t = delta_(i j)$
])
#note-box([
  Deduciamo dunque che una matrice ortogonale è facilmente invertibile e che la sua trasposta è anch'essa ortogonale. Inoltre, se $A in O(n)$, poiché $A dot A^t = I$, $det(A dot A^t) = det(A) dot det(A^t) = det(A)^2 = det(I) = 1$, quindi $det(A) = plus.minus 1$. Infine, se $A, B in O(n)$, anche $A dot B in O(n)$.
])
#definition(title: [Isometria], [
  Sia $(V, plus, dot, RR, pscal(dot, dot))$ euclideo. $f: V -> V$ si dice _isometria_ se $norm(u - v) = norm(f(u) - f(v)), forall u, v in V$
])
#theorem(title: [Isometria come trasformazione affine], [
  Sia $f: V -> V$ un'isometria. Allora $f(v) = T(v) + v_0$ dove $T$ è un'isometria lineare.
])

== Endomorfismi simmetrici

#definition(title: [Endomorfismo simmetrico], [
  Sia $(V, +, dot, RR, pscal(dot, dot))$ euclideo. $T: V -> V$ si dice _simmetrico_ se $pscal(T(u), v) = pscal(u, T(v)), forall u, v in V$.
])
#note-box([
  Gli endomorfismi simmetrici non preservano la metrica.
])
Per la definizione, se consideriamo $u, v in V$, una base $o.n. " " B$ e $A = M_B^B (T)$, abbiamo che
$
  pscal(T(u), v) = pscal(u, T(v)) <=> [A dot u]_B^t dot [v]_B = [u]_B^t dot [A dot v]_B <=>[u]_B^t dot A^t dot [v]_B = [u]_B^t dot A dot [v]_B
$
Poiché sappiamo che $e_i^t dot M dot e_j = M_(i j)$, allora
$
  e_i^t dot A^t dot e_j = e_i^t dot A dot e_j <=> (A^t)_(i j) = A_(i j) <=> A^t = A
$
ossia la matrice rappresentativa $M_B^B (T)$ di un endomorfismo simmetrico è simmetrica.
#theorem(
  title: [Simmetria della matrice rappresentativa di un endomorfismo simmetrico],
  [
    $T: attach(V, tl: B) -> V^B'$ un endomorfismo con $B, B' " " o.n.$ $T$ è simmetrico se e solo se $M_B^B' (T)$ è simmetrica.
  ],
) <spe:ses>
#warning-box([
  Si può riconoscere un endomorfismo simmetrico dalla sua matrice rappresentativa solo quando si hanno basi $o.n.$, come nel caso delle isometrie.
])
#definition(title: [Endomorfismo ortogonalmente diagonalizzabile], [
  Sia $T: V -> V$ un endomorfismo. $T$ si dice _ortogonalmente diagonalizzabile_ se esiste una base $o.n.$ di $V$ fatta di autovettori.
])

#corollary(title: [Simmetria di un endomorfismo diagonalizzabile], [
  Se $T: attach(V, tl: B) -> V^B$ è ortogonalmente diagonalizzabile, allora $T$ è simmetrico.
])
#proof([
  Poiché $B$ è base di autovettori, $M_B^B (T) = d i a g(lambda_1, ..., lambda_n) <=> M_B^B (T) = (M_B^B (T))^t$. Quindi, per il @spe:ses, $T$ è simmetrico.
])
#lemma(title: [Radici del polinomio di un endomorfismo simmetrico], [
  Sia $T: V -> V$ un endomorfismo simmetrico. Allora $p_T (x)$ ha $dim(V)$ radici reali contate con la loro molteplicità.
]) <spe:res>

== Teorema spettrale

#proposition(title: [Ortogonalità di autospazi], [
  Siano $T: V -> V$ un endomorfismo simmetrico e $lambda, mu in sigma(T)$ con $lambda != mu$. Allora $V_lambda perp V_mu$.
]) <spe:oda>
#proof([
  Siano $u in V_lambda, v in V_mu$. Allora $lambda pscal(u, v) = pscal(lambda u, v) = pscal(T(u), v)$. Poiché $T$ è simmetrico, $pscal(T(u), v) = pscal(u, T(v)) = pscal(u, mu v) = mu pscal(u, v) <=> lambda pscal(u, v) = mu pscal(u, v) <=> (lambda - mu)pscal(u, v) = 0 <=> pscal(u, v) = 0$ \ $<=> u perp v <=> V_lambda perp V_mu$
])

#theorem(title: [Teorema spettrale], [
  Sia $T: V -> V$ un endomorfismo. $T$ è simmetrico se e solo se è ortogonalmente diagonalizzabile.
])
#proof([
  Supponiamo che $T$ sia simmetrico e che $n = dim(V)$. Consideriamo $n = 1$. Allora $V = cal(L) (v_1)$ dove $v_1 != cal(O)_V$ e $T(v_1) in cal(L) (v_1)$, ossia $T(v_1) = k v_1$. Quindi possiamo dire che ${b_1}$, dove $b_1 = v_1 / norm(v_1)$, è una base $o.n.$ di $V$ di autovettori, quindi $T$ è ortogonalmente diagonalizzabile se $n = 1$. \
  Supponiamo ora che ogni endomorfismo simmetrico $F: W -> W$ con $dim(W) <= n - 1$ sia ortogonalmente diagonalizzabile. \
  Per il @spe:res, esiste almeno un autovalore reale $lambda$ di $T$. Consideriamo l'autovettore $b_1 in V_lambda$ con $norm(b_1) = 1$, $U = cal(L) (b_1)$ e $W = U^perp$. Sappiamo che $T(W) subset.eq W$ se $forall w in W, T(w) in W <=> pscal(T(w), b_1) = 0$, poiché $b_1 in U$ e $W = U^perp$, quindi $b_1 perp W$. Allora $pscal(T(w), b_1) = pscal(w, T(b_1)) = pscal(w, lambda b_1) = lambda pscal(w, b_1) = 0$, quindi $T(w) perp b_1 => T(w) in W$. \
  Per la @spe:pco, $V = W plus.o U$, quindi $dim(W) = dim(V) - dim(U) = n - 1$. Inoltre, poiché $T$ è simmetrico su $V$, lo è anche su $W$. Allora, per la precedente supposizione, $T: W -> W$ è ortogonalmente diagonalizzabile, e la base $o.n.$ di $W$ fatta di autovettori è ${b_2, ..., b_n}$. Poiché $b_1$ è autovettore di $T$ e $b_1 in U = W^perp$, ${b_1, b_2, ..., b_n}$ sono ortogonali, e, poiché abbiamo $n$ vettori, sono autovettori, quindi sono una base $o.n.$ di $V$. Abbiamo dunque che $T$ è ortogonalmente diagonalizzabile.
])
#pagebreak()

Quindi, possiamo definire un algoritmo che, dato un endomorfismo $T: V -> V$ e una base ortonormale $B$ di $V$, ci permette di trovare una base ortonormale $B'$ di $V$ fatta di autovettori, che procede:
1. Costruisco $A = M_B^B (T)$. Se $A$ è simmetrica (ossia $A = A^t$), allora $T$ è simmetrico, quindi, per il teorema spettrale, è anche ortogonalmente diagonalizzabile
2. Calcolo lo spettro $sigma(T) = {lambda_1, ..., lambda_l}$.
3. Con la relazione $[V_lambda_i]_B = ker (A - lambda_i I)$ calcolo una base $B_i = {[u_1]_B, ..., [u_k]_B}$ per ogni autospazio $V_lambda_i$ e uso Gram-Schmidt per ortonormalizzarla ottenendo $B'_i = {[v_1]_B, ..., [v_k]_B}$
4. Se considero l'unione di queste basi, ottengo $display(union.big^l_(i = 1)) B'_i = {[v_1]_B, ..., [v_n]_B}$, quindi la base $B'$ che cerco è esattamente $B' = {v_1, ..., v_n}$
5. La matrice di cambio base è $P = M_B'^B (I d) = ([v_1]_B | ... | [v_n]_B)$. Poiché $B$ e $B'$ sono ortonormali, allora $P$ è ortogonale, ossia $P^(-1) = P^t$. Quindi $P^t A P = P^(-1) A P$ è diagonale.
#note-box([
  $l$ rappresenta il numero di autovalori distinti di $T$, $k$ rappresenta la molteplicità geometrica di un certo autovalore, mentre $n$ è la dimensione di $V$. \
  Se considero una matrice $A$ e l'endomorfismo ad essa associata $L_A: RR^n -> RR^n$, ho che  se $A$ è simmetrica, poiché la base canonica è $o.n.$ e $M_epsilon^epsilon (L_A) = A = A^t$, anche $L_A$ è simmetrica, quindi il teorema spettrale mi garantisce che esiste una matrice di cambio base $P$ ortogonale tale che $P^t A P$ è diagonale.
])

#proposition(title: [Proprietà di matrici simmetriche], [
  Sia $A$ una matrice. Se $A = A^t$, allora $exists P in O(n) : P^t A P = d i a g (lambda_1, ..., lambda_n)$.
]) <spe:pms>
#theorem(title: [Decomposizione spettrale], [
  Siano $T: V -> V$ simmetrico con $sigma(T) = {lambda_1, ..., lambda_l}$ e $P_V_lambda_i$ la proiezione ortogonale sull'autospazio $V_lambda_i$. Allora $T = display(sum^l_(i = 1)) lambda_i P_V_lambda_i$ e $M_B^B (T) = display(sum^l_(i = 1)) lambda_i M_B^B (P_V_lambda_i)$.
])

= Forme quadratiche

#definition(title: [Forma quadratica], [
  Una funzione $q(x): RR^n -> RR$ definita come la somma di monomi solamente di 2° grado, ossia $q(x) = q(x_1, ..., x_n) = display(sum^n_(i, j = 1)) a_(i j) x_i x_j$ è detta _forma quadratica_.
])
Data una forma quadratica $q(x)$, esiste sempre una matrice simmetrica $B$ tale che $q(x) = x^t B x$, la quale è definita come $b_(i j) = b_(j i) = (a_(i j) + a_(j i)) / 2$. Da questo deduciamo anche che $q(underline(0)) = 0$ e $q(t x) = t^2 q(x)$.
#pagebreak()
#definition(title: [Segno di una forma quadratica], [
  Una forma quadratica $q(x) = x^t B x$ con $B = B^t$ si dice:
  - _definita positiva_ se $q(x) > 0, forall x in RR^n \\ {underline(0)}$
  - _definita negativa_ se $q(x) < 0, forall x in RR^n \\ {underline(0)}$
  - _semidefinita positiva_ se $q(x) >= 0, forall x in RR^n$ e $exists y in RR^n \\ {underline(0)} : q(y) = 0$
  - _semidefinita negativa_ se $q(x) <= 0, forall x in RR^n$ e $exists y in RR^n \\ {underline(0)} : q(y) = 0$
  - _indefinita_ se $exists x, y in RR^n : q(x) < 0, q(y) > 0$
])
#definition(title: [Segnatura di una forma quadratica], [
  Sia $q(x) = x^t B x$ una forma quadratica con $B in MM_(n,n) (RR)$. Si dice _segnatura di $q(x)$_ la terna di numeri naturali $(n_+, n_-, n_0)$, dove:
  - $n_+$ è la dimensione massima del sottospazio $V_+ subset.eq RR^n$ tale che $q(x) > 0, forall x in V_+ \\ {underline(0)}$
  - $n_-$ è la dimensione massima del sottospazio $V_- subset.eq RR^n$ tale che $q(x) < 0, forall x in V_- \\ {underline(0)}$
  - $n_0 = n - (n_+ + n_-)$
])
Deduciamo dunque che quando la segnatura è del tipo, con $a + b + c = n$ e $a, b != n$:
- $(n, 0, 0)$: definita positiva
- $(0, n, 0)$: definita negativa
- $(a, 0, b)$: semidefinita positiva
- $(0, a, b)$: semidefinita negativa
- $(a, b, c)$: indefinita

#definition(title: [Matrici congruenti], [
  Due matrici $A, B in MM_(n,n) (RR)$ si dicono _congruenti_ se $exists C in MM_(n,n)(RR) "invertibile" : B = C^t A C$.
])
Se infatti consideriamo l'isomorfismo $T: RR^n -> RR^n$ dove $y = T(x) = C^(-1) x$, abbiamo che $x = C y$. Dunque $q(x) = x^t B x = (C y)^t B (C y) = y^t (C^t B C) y = y^t B' y = q'(y)$ con $B$ e $B'$ entrambe matrici quadrate e congruenti. Inoltre, poiché $T$ è biunivoca, $q(x) gt.lt 0, forall x in V_plus.minus <=> q'(y) gt.lt 0, forall y in T(V_plus.minus)$, e, poiché $T$ è un isomorfismo, $dim(T(V_plus.minus)) = dim(V_plus.minus)$, quindi le segnature di $q(x)$ e $q'(y)$ coincidono.

#theorem(title: [Equivalenza tra segnature di forme quadratiche], [
  Siano $q(x) = x^t B x$ e $q'(y) = y^t B' y$ due forme quadratiche con $B, B' in MM_(n,n)(RR)$. Se $B$ e $B'$ sono congruenti, allora $q(x)$ e $q'(y)$ hanno la stessa segnatura.
]) <fmq:sfq>
#pagebreak()
== Teorema di inerzia

L'esempio più semplice di forma quadratica è $q(x) = x_1^2 + ... + x_p^2 - x_(p + 1)^2 - ... - x_(p + k)^2 = x^t S x$. In questo caso, la matrice $S$ è detta *forma normale di Sylvester*, ed assume questa forma
$
  S = mat(
    1; , dots.down; , , 1;
    , , , -1; , , , , dots.down; , , , , , -1;
    , , , , , , 0; , , , , , , , dots.down; , , , , , , , , 0;
  ) = mat(I_p; , -I_k; , , 0 I_0)
$
Si ha che $V_+ = cal(L) (e_1, ..., e_p)$ e $V_- = cal(L) (e_(p + 1), ..., e_(p + k))$, quindi $S$ ha segnatura $(p, k, n - (p + k))$.

#theorem(title: [Teorema di inerzia di Sylvester], [
  Sia $B in MM_(n,n)(RR)$ una matrice simmetrica, ossia $B = B^t$. Allora:
  1. $B$ è congruente alla matrice $S = d i a g(I_p, -I_k, 0 I_0)$, dove $p$ e $k$ sono il numero di autovalori rispettivamente positivi e negativi contati con la loro molteplicità, mentre $n - (p + k) = m_a (0)$
  2. la segnatura di $q(x) = x^t B x$ è $(p, k, m_a (0))$
  3. un possibile sottospazio massimale $V_+$ su cui $q(x)$ è definita positiva è dato dalla somma diretta degli autospazi degli autovalori positivi, ossia $V_+ = V_lambda_1 plus.o ... plus.o V_lambda_p$ e, analogamente, un possibile $V_- = V_lambda_(p + 1) plus.o ... plus.o V_lambda_(p + k)$

])
#proof([
  1. Per la @spe:pms, $exists P in O(n) : P^t B P = d i a g(lambda_1, ..., lambda_p, lambda_(p + 1), ..., lambda_(p + k), ..., 0)$ $= D$, dove $D$ e $B$ sono congruenti grazie a $P$, quindi sono invertibili. Considero la matrice $F = d i a g(1 / sqrt(abs(lambda_1)), ..., 1 / sqrt(abs(lambda_(p + k))), ..., 1)$, anch'essa invertibile e simmetrica. Inoltre $F^t (P^t B P) F = F^t D F = F D F = S$, poiché $lambda_i / (sqrt(abs(lambda_i)))^2 = plus.minus 1$. Quindi $(P F)^t B (P F) = S$. Consideriamo la matrice $C = P F$, la quale è invertibile, e sappiamo che $C^t B C = S$, quindi $B$ è congruente ad $S$
  2. Per il @fmq:sfq, $q(x)$ ha segnatura $(p, k, m_a (0))$
  3. Siano $u_i in V_lambda_i, v = u_1 + ... + u_p, v != cal(O)_V$. Per la @spe:oda, $$, con $i != j$ si ha che $V_lambda_i perp V_lambda_j$, quindi $u_i^t u_j = 0$. Perciò otteniamo che $q(v) = (u_1 + ... + u_p)^t B (u_1 + ... + u_p) = (u_1 + ... + u_p)^t (B u_1 + ... + B u_p) = (u_1^t + ... + u_p^t)(lambda_1 u_1 + ... + lambda_k u_p) = lambda_1 norm(u_1)^2 + ...$ $+ lambda_p norm(u_p)^2$. Poiché $lambda_i norm(u_i)^2 > 0, forall i = 1, ..., p$, anche $q(v) > 0$, quindi $V_+ = V_lambda_1 plus.o ... plus.o V_lambda_p$
])
#theorem(title: [Criterio di Cartesio], [
  Sia $p(x) = a_n x^n + ... + a_d x^d$ un polinomio. Se $p(x)$ ha tutte radici reali, allora:
  - $0$ è radice se e solo se $d >= 1$, quindi $d = m_a (0)$
  - $p(x)$ ha tante radici positive contate con la loro molteplicità quante sono le variazioni di segno dei coefficienti $a_i$ non nulli
])

== Classificazione di ipersuperfici quadriche

#definition(title: [Ipersuperficie quadrica], [
  Il sottoinsieme $Q = {x = vec(x_1, dots.v, x_n) in RR^n : q(x) = 0}$ dove $q(x)$ è un polinomio di 2° grado tale che $q(x) = display(sum^n_(i,j = 1)) a_(i j) x_i x_j + 2 display(sum^n_(j = 1)) b_j x_j + c$ e $a_(i j), b_j, c in RR$ si dice _ipersuperficie quadrica di $RR^n$_.
])
Possiamo scomporre l'espressione di un'ipersuperficie quadrica in una *forma quadratica* (la prima sommatoria), una *parte lineare* (la seconda sommatoria) ed una *costante* (la $c$).

In particolare, in $RR^2$ le ipersuperfici quadriche si dicono *coniche* e in $RR^3$ si dicono *quadriche*.

In forma matriciale, un'ipersuperficie quadrica assume le forme:
- $q(x) = x^t B x + 2b^t x + c = 0$ dove $b = vec(b_1, dots.v, b_n)$
- $q(x) = (x_1 " " ... " " x_n " " 1) mat(B, b; b^t, c) vec(x_1, dots.v, x_n, 1) = 0$

In generale, dati due sistemi di riferimento $R(O, B)$ e $R'(v_0, B')$, un punto $Q$ è descritto sia da $[v]_B = vec(x_1, dots.v, x_n) = x$ che da $[u]_B' = vec(y_1, dots.v, y_n) = y$. Quindi posso passare da $x$ a $y$, considerando $P = M_B^B' (I d)$:
$
  y = [u]_B' = [v - v_0]_B' = P [v - v_0]_B = P [v]_B - P [v_0]_B = P x - P[v_0]_B
$
Dunque la trasformazione di coordinate $f: RR^n -> RR^n$ è la trasformazione affine $f(x) = P x - v'_0$. Questo cambio di sistema di riferimento ci permette di *classificare* coniche e quadriche, in quanto semplifica l'equazione e la rende più semplice da riconoscere. \
Se $P$ è solo invertibile, allora parliamo di *classificazione affine*. Se è anche ortogonale, parliamo invece di *classificazione metrica*.

#note-box([
  Con la classificazione metrica, utilizziamo un'isometria per passare da un sistema fi riferimento all'altro, in modo tale da non avere deformazioni, le quali invece si hanno con le trasformazioni affini, anche se comunque si mantengono certe caratteristiche.
])

=== Quadriche a centro

Consideriamo la quadrica $Q = {x in RR^n : q(x) = x^t B x + 2 b^t x + c = 0}$.

$Q$ ha una simmetria centrale rispetto a $underline(0)$ se e solo se $q(x) = q(-x) = 0 <=> cancel(x^t B x) + 2 b^t x + cancel(c) = cancel(x^t B x) - 2 b^t x + cancel(c) <=> 4 b^t x = 0 <=> b^t x = 0$, ossia si ha una simmetria centrale se la quadrica possiede una parte lineare nulla.
#pagebreak()
Per eliminare la parte lineare, posso partire applicando una *traslazione* a $q(x)$, ossia un'isometria non lineare ($tau_(-v_0): RR^n -> RR^n$). Considerando $y = x - v_0$ ottengo
$
  q(x) = 0 <=> 0 &= q(y + v_0) = (y + v_0)^t B (y + v_0) + 2b^t (y + v_0) + c = \
  &= y^t B y + underbrace(v_0^t B y + y^t B v_0, "scalari" <=> k = k^t) + v_0^t B v_0 + underbrace(2 b^t y, "scalare") + 2 b^t v_0 + c = \
  &= y^t B y + (v_0^t B y)^t + y^t B v_0 + v_0^t B v_0 + (2 b^t y)^t + 2b^t v_0 + c = \
  &= y^t B y + y^t underbrace(B^t, = B) v_0 + y^t B v_0 + v_0^t B v_0 + 2 y^t b + 2 b^t v_0 + c = \
  &= y^t B y + 2 y^t (B v_0 + b) + underbrace(v_0^t B v_0 + 2 b^t v_0 + c, "costante") = y^t B y + 2y^t (B v_0 + b) + display(op(c, limits: #true)^~)
$
Quindi per eliminare la parte lineare devo cercare un $v_0$ che soddisfi $B v_0 + b = 0 <=> B v_0 = -b$. Se questo $v_0$ esiste, lo diciamo *centro* e otteniamo che la traslazione $y = tau_(-v_0) (x) = x - v_0$ trasforma $q(x) = x^t B x + 2 b^t x + c$ in $q'(y) = y^t B y + display(op(c, limits: #true)^~)$ dove $display(op(c, limits: #true)^~) = v_0^t underbrace(B v_0, -b) + 2 b^t v_0 + c = -v_0^t b + 2 b^t v_0 + c = -b^t v_0 + 2b^t v_0 + c = b^t v_0 + c$.
#definition(title: [Quadrica a centro], [
  Una quadrica $Q$ si dice _a centro_ se ha almeno un centro di simmetria, ossia se $S o l(B, -b) != emptyset$. Questo insieme di soluzioni è anche indicato $epsilon (Q)$ ed è l'insieme dei centri di $Q$.
])
Poiché $B$ è simmetrica, dalla @spe:pms $exists P in O(n) : P = M_C^epsilon (I d)$ dove $C$ è base $o.n.$ di autovettori, grazie alla quale otteniamo la matrice diagonale $P^t B P = mat(lambda_1; , dots.down; , , lambda_n) = D$.

Considero dunque l'isometria lineare $T_2: RR^n -> RR^n$ tale che $z = T_2 (y) = P^t y <=> y = P z$. Ottengo
$
  q'(y) = q'(P z) = (P z)^t B (P z) + display(op(c, limits: #true)^~) = z^t (P^t B P) z + display(op(c, limits: #true)^~) = z^t D z + display(op(c, limits: #true)^~) \
  <=> q''(z) = (z_1 " " ... " " z_n) mat(lambda_1; , dots.down; , , lambda_n) vec(z_1, dots.v, z_n) + display(op(c, limits: #true)^~) = lambda_1 z_1^2 + ... + lambda_n z_n^2 + display(op(c, limits: #true)^~) = 0
$
La nostra quadrica a centro ha evidentemente assunto una forma decisamente più semplice, e questa trasformazione è stata possibile trovando prima il suo centro $v_0$ e poi applicando due isometrie.

#definition(title: [Forma canonica metrica di una quadrica a centro], [
  La forma canonica metrica di una quadrica a centro è
  $q''(z) = display(cases(lambda_1 z_1^2 + ... + lambda_r z_r^2 = 0 &"se" display(op(c, limits: #true)^~) = 0, lambda_1 / display(op(c, limits: #true)^~) z_1^2 + ... + lambda_r / display(op(c, limits: #true)^~) z_r^2 + 1 = 0 &"se" display(op(c, limits: #true)^~) != 0))$ \ dove $r = n_+ + n_-$.
])
#pagebreak()

=== Quadriche non a centro

$Q$ non è a centro se $S o l(B, -b) = emptyset$, quindi $det(B) = 0$ e $b in.not W = cal(L) (C o l(B))$. Però, posso considerare la migliore approssimazione di $b$ che sicuramente è in $W$, ossia la sua proiezione $P_W (b)$.
#proposition(title: [Proprietà del "sistema approssimato"], [
  Se $B$ è simmetrica, il sistema $B v_0 = - P_W (b)$ con $W = cal(L) (C o l(B))$ soddisfa:
  1. $ker(B^2) = ker(B)$
  2. $S o l(B, -P_W (b)) = S o l(B^2, -B b) = v_0 + ker(B^2) = v_0 + ker(B)$
  3. $W^perp = ker(B)$
])
#proof([
  3. $W^perp = cal(L) (C o l(B))^perp$. Poiché $B = B^t$, $= cal(L) (R i g(B))^perp = {x in RR^n : B x = underline(0)} = ker(B)$
])
#definition(title: [Asse di una quadrica non a centro], [
  L'insieme $A x(Q) = S o l(B, -P_W (b)) = S o l(B^2, -B b) = v_0 + ker(B)$ è detto _asse_ di $Q$.
])

Applicando la stessa traslazione $tau_(-v_0)$ di prima, con $y = x - v_0$ e con $v_0 in A x(Q)$, ottengo
$
  q'(y) = y^t B y + 2 y^t underbrace((b + B v_0), b - P_W (b)) + underbrace(v_0^t B v_0 + 2 b^t v_0 + c, display(op(c, limits: #true)^~)) = 0 \
  b + B v_0 = b - P_W (b) = P_(W^perp) (b) op(=^(W^perp = ker(B))) P_ker(B) (b) = b_0 => q'(y) = y^t B t + 2 y^t b_0 + display(op(c, limits: #true)^~) = 0
$
Successivamente effettuo un cambio base alla stessa maniera di prima, considerando $P = M_B'^epsilon (I d)$ e $z = P^t y <=> y = P z$, dove $B' = {b_1, ..., b_r, b_(r + 1), ..., b_n}$ dove $b_1, ..., b_r$ sono gli autovettori relativi ad autovalori non nulli e $b_(r + 1), ..., b_n$ sono una base $o.n.$ di $ker(B)$ costruita a partire da $b_(r + 1) = b_0 / norm(b_0)$.
$
  q''(z) = z^t (P^t B P) z + 2 z^t P^t b_0 + display(op(c, limits: #true)^~) = 0 \
  <=> 0 = q''(z) = z^t D z + 2 z^t inline(vec(0, dots.v, 0, norm(b_0), 0, dots.v, 0)) + display(op(c, limits: #true)^~) = z^t D z + 2 norm(b_0) z_(r + 1) + display(op(c, limits: #true)^~)
$
Infine applico una traslazione per eliminare $display(op(c, limits: #true)^~)$. Considero $w = z + (0 " " ... " " 0 " " display(op(c, limits: #true)^~) / (2norm(b_0)) " " 0 " " ... " " 0)$ e ottengo
$
  q'''(w) = w^t D w + 2 norm(b_0) w_(r + 1) = lambda_1 w_1^2 + ... + lambda_r w_r^2 + 2 norm(b_0) w_(r + 1) = 0
$
#definition(title: [Forma canonica metrica di una quadrica non a centro], [
  La forma canonica metrica di una quadrica non a centro è $q'''(w) = lambda_1 w_1^2 + ... + lambda_r w_r^2 + 2 norm(b_0) w_(r + 1) = 0$ dove $r = n_+ + n_-$ e $b_0 = P_ker(B)(b)$.
])
#pagebreak()

In conclusione, data una generica quadrica $Q: q(x) = x^t B x + 2 b^t x + c$:
- *Ha centro* se e solo se $S o l(B, -b) != emptyset$
  1. Calcolo un centro $v_0 in S o l(B, -b)$
  2. Calcolo $display(op(c, limits: #true)^~) = b^t v_0 + c$
  3. Calcolo gli autovalori di $B$ $lambda_1, ..., lambda_r$ dove $r = n_+ + n_-$
  4. La forma canonica metrica è $cases(lambda_1 z_1^2 + ... + lambda_r z_r^2 = 0 &"se" display(op(c, limits: #true)^~) = 0, lambda_1 / display(op(c, limits: #true)^~) z_1^2 + ... + lambda_r / display(op(c, limits: #true)^~) z_r^2 + 1 = 0 &"se" display(op(c, limits: #true)^~) != 0)$
- *Non ha centro* se e solo se $S o l(B, -b) = emptyset$
  1. $b_0 = P_ker(B) (b)$
  2. Calcolo gli autovalori di $B$ $lambda_1, ..., lambda_r$
  3. La forma canonica metrica è $lambda_1 x_1^+ ... + lambda_r x_r^2 + 2 norm(b_0) x_(r + 1) = 0$

=== Classificazione affine

Si può effettuare un ulteriore semplificazione, ma questo comporta l'utilizzo di trasformazioni affini di coordinate.
Consideriamo $q''(z) = z^t D z + display(op(c, limits: #true)^~)$. Se $display(op(c, limits: #true)^~) = 0$, allora posso applicare la trasformazione affine $T_3 (z) = C z$ dove $C = d i a g(sqrt(abs(lambda_1)), ..., sqrt(abs(lambda_n)), 1, ..., 1)$, la quale è invertibile, quindi $z = C^(-1) w$.
$
  q''(z) = q''(C^(-1) w) = w^t (C^(-1))^t D C^(-1) w op(=^((C^(-1))^t = C^(-1))) w^t mat(lambda_1 / abs(lambda_1); , dots.down; , , lambda_n / abs(lambda_n); , , , 0; , , , , dots.down; , , , , , 0) w = w^t S w
$
Si può effettuare un processo analogo se $display(op(c, limits: #true)^~) = 0$: si applica $w = T_3 (z) = C z$ a $q''(z) = 1/display(op(c, limits: #true)^~) (z^t D z) + 1$ considerando $C = d i a g(sqrt(abs(lambda_1 / display(op(c, limits: #true)^~))), ..., sqrt(abs(lambda_n / display(op(c, limits: #true)^~))), 1, ..., 1)$.

#definition(title: [Forma canonica affine di una quadrica a centro], [
  La forma canonica affine di una quadrica a centro è $q'''(w) = w_1^2 + ... + w_s^2 - w_(s + 1)^2 - ... - w_(s + t)^2 + display(cases(0 &"se" display(op(c, limits: #true)^~) = 0, 1 &"se" display(op(c, limits: #true)^~) != 0))$, dove $(p, k, n - (p + k))$ è la segnatura e $display(cases(s = p\, t = k &"se" display(op(c, limits: #true)^~) >= 0, s = k\, t = p &"se" display(op(c, limits: #true)^~) < 0))$.
])
Consideriamo ora $q'''(w) = w^t D w + 2 norm(b_0) w_(r + 1)$. Se applico la dilatazione $u = T_4 (w) = C w$ dove $C = d i a g(sqrt(abs(lambda_1)), ..., sqrt(abs(lambda_n)), norm(b_0), 1, ..., 1)$, quindi $w = C^(-1) u$, otteniamo $q''''(u) = q'''(C^(-1) u)$.
#definition(title: [Forma canonica affine di una quadrica non a centro], [
  La forma canonica affine di una quadrica non a centro è $q''''(u) = u_1^2 + ... + u_p^2 - u_(p + 1)^2 - ... - u_(p + k)^2 + 2u_(p + k + 1)$ dove $(p, k, n - (p + k))$ è la segnatura.
])

In conclusione, data una generica quadrica $Q: q(x) = x^t B x + 2b^t x + c$:
- *Ha centro* se e solo se $S o l(B, -b) != emptyset$
  1. Calcolo il segno di $display(op(c, limits: #true)^~) = b^t v_0 + c$ e calcolo la segnatura $(p, k, n - (p + k))$ di $B$
  2. $q(x) = w_1^2 + ... + w_s^2 - w_(s + 1)^2 - ... - w_(s + t)^2 + display(cases(0 &"se" display(op(c, limits: #true)^~) = 0, 1 &"se" display(op(c, limits: #true)^~) != 0)) = 0$ con $display(cases(s = p\, t = k &"se" display(op(c, limits: #true)^~) >= 0, s = k\, t = p &"se" display(op(c, limits: #true)^~) < 0))$
- *Non ha centro* se e solo se $S o l(B, -b) = emptyset$ \
  $=> q(x) = x_1^2 + ... + x_p^2 - x_(p + 1)^2 - ... - x_(p + k)^2 + 2x_(p + k + 1) = 0$


#pagebreak()
#outline(
  title: [Indice dei dimostrabili],
  target: figure
    .where(kind: "theorem")
    .or(figure.where(kind: "proposition"))
    .or(figure.where(kind: "lemma"))
    .or(figure.where(kind: "corollary")),
)

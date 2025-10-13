#import "@preview/theorion:0.3.3": *

#import cosmos.rainbow: *

#show: show-theorion

#set text(lang: "it")
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
#pagebreak()
#theorem(
  title: [Esistenza di una base],
  [
    Se lo spazio $(V, +, dot, KK)$ è finitamente generato, allora esiste una base finita.
  ],
)
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
#proposition([Le mosse di Gauss preservano $S o l(A)$])
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
    2. se $exists alpha in S o l(A, b)$ allora $S o l(A, b) = alpha + ker(A) = {beta in KK^n : beta = alpha + t_1 v_1 + ... + t_s v_s, forall t_i in KK, v_i in ker(A), s = n - r k(A)}$
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
#pagebreak()
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
)
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
#theorem(title: [Teorema del rango], [
  $ dim(cal(L)(C o l(A))) = dim(cal(L)(R i g(A))) = r k(A) $
])
#warning-box([$cal(L)(C o l(A))$ non si preserva quando riduco $A$ a scala.])

#proposition(
  title: [Estrazione di base con riduzione a scala],
  [
    Siano $B = (v_1 | ... | v_n)$ una matrice con $v_1, ..., v_n in KK^m$, $I = {j_1, ..., j_k}$ l'insieme degli indici di colonna dei pivot di $B$ ridotta a scala. Allora $B = {v_j_i, j_i in I}$ è base di $cal(L)(v_1, ..., v_n)$.
  ],
)

#pagebreak()
#outline(title: [Indice dei dimostrabili], target: figure
  .where(kind: "theorem")
  .or(figure.where(kind: "proposition"))
  .or(figure.where(kind: "lemma")))

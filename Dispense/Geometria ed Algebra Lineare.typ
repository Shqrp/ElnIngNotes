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

= Gli spazi vettoriali

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
  title: [Spazio vettoriale],
  [
    Sia $(KK, +, dot, 0, 1)$ un campo vettoriale. $V$ si dice _spazio vettoriale_ sul campo $KK$ se:
    - $V$ è un insieme di vettori
    - all'interno di $V$ si può svolgere l'operazione binaria interna di _somma_, la quale soddisfa le proprietà associativa e commutativa, ha elemento neutro ($cal(O) = (0, 0, 0)$) e inverso ($exists w in V : v + w = 0, forall v in V$).
    - all'interno di $V$ si può svolgere l'operazione binaria esterna di _prodotto per uno scalare_ ($KK times V -> V$), la quale soddisfa le proprietà distributiva di $dot$ su $+$ e associativa e ha l'$1$ come elemento neutro
  ],
)

In generale $(RR^n, +, dot, R)$ è uno spazio vettoriale. \ \ \ \ \ \

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

= Geometria nel piano e nello spazio

In generale, per $AA_1$ si intende l'*insieme dei punti sulla retta affine*, per $AA_2$ l'*insieme dei punti sul piano affine* e per $AA_3$ l'*insieme dei punti nello spazio affine*.

#definition(
  title: [Vettore],
  [Un vettore è un $n$-upla ordinata di punti, i quali appartengono allo stesso insieme. Dati $A in RR^2$ e $BB in RR^2$, si denota come $(A, B), A B, arrow(A B), underline(A B), B - A, ...$],
)
Un vettore ha un *verso*, una *direzione* e una *norma*, ossia la sua lunghezza (denotata come $norm(A B)$). \
Due vettori si dicono *equipollenti* se con una traslazione posso sovrapporli, dunque se hanno norma, direzione e verso coincidenti.

#definition(
  title: [Insiemi di vettori],
  [Fissato un punto $O$ di origine, denotiamo con $V_0^1$ l'_insieme dei vettori della retta affine_ con origine $O$, $V_0^2$ l'_insieme dei vettori del piano affine_ con origine $O$, e $V_0^3$ l'_insieme dei vettori dello spazio affine_ con origine $O$.],
)
#note-box([Ad ogni vettore corrisponde un vettore centrato nell'origine a lui equipollente. ($exists! O B' ~ A B, forall A B in RR^2$). \ Ogni punto appartenente al retta/piano/spazio affine può essere individuato da un vettore centrato nell'origine.])

Per sommare due vettori centrati nello stesso punto, si utilizza la *regola del parallelogramma*.
$ O A + O B := O C, O C ~ A B $
Si dimostra dunque che $(V_0^2, +)$ è un gruppo commutativo:
- vale la proprietà associativa: $O A + (O B + O C) = (O A + O B) + O C$
- vale la proprietà commutativa: $O A + O B = O B + O A$
- esiste l'elemento neutro: $exists cal(O) = O O : O A + O O = O A$
- esiste l'inverso: $(O, A) = -(O, -A)$ \

Il prodotto per uno scalare si definisce come $RR times V_0^2 -> V_0^2$. Il vettore risultato del prodotto di $v in V_0^2$ per uno scalare $t in RR$ è il vettore con uguale direzione, norma moltiplicata per t e verso concorde per $t >= 0$ e discorde per $t <= 0$.

== Il sistema di riferimento

Per poter descrivere un punto $P$ su una retta è necessario avere un *sistema di riferimento*. Fissiamo dunque un qualsiasi punto $O$ sulla retta come *origine* del sistema e un qualsiasi vettore $v$ che indica la direzione del sistema di riferimento: come risultato otteniamo $R(O, v)$.\
Dunque il punto $P$ può essere individuato tramite il vettore $O P in V_0^1 = 2 dot v$, dove il $2$ rappresenta l'unica coordinata del punto. Quindi, fissato $R(O, v)$, possiamo dire che $P = (3)$. \

Nel caso del piano affine, bisogna aggiungere al sistema un secondo vettore $u$ che non sia parallelo a $v$ (ossia $v != t dot u, forall t in RR$), ottenendo quindi $R(O, v, u)$. \
Dato un qualsiasi punto $Q$ nel piano con coordinate $(2, 2)$, esso sarà individuato dal vettore \ $O Q in V_0^2 = 2 dot v + 2 dot u$, ossia come *combinazione lineare* tra $vec(v, u)$ e $vec(2, 2)$. Analogamente, nel caso dello spazio affine va introdotto un terzo vettore $w$ tale che $v, u, w$ non siano complanari (ossia $w != t dot v + s dot u, forall t, s in RR$).

=== Sistema di riferimento ortonormale

Per poter semplificare i calcoli, si può introdurre un sistema di riferimento *ortonormale*, ossia con vettori lunghi $1$ e perpendicolari fra loro. Per esempio, ora è possibile calcolare la norma di un vettore utilizzando il teorema di Pitagora ($O A = (a, b, c), norm(O A)^2 = a^2 + b^2 + c^2$) oppure calcolare il coseno dell'angolo compreso tra due vettori ($O B = (d, e, f), cos theta = (O A dot O B)/(norm(O A) dot norm(O B))$).

== Rette e piani in $AA_3$

In generale, una retta è definita come l'insieme dei punti i cui vettori associati fissati nell'origine sono il risultato della somma tra un punto noto che appartiene alla retta e un *vettore direttore* moltiplicato per un parametro $t in RR$, dunque l'espressione è detta *equazione parametrica*.
#definition(title: [Retta in $AA_3$], [
  $ r := {P : O P tilde.eq vec(x, y, z) = vec(x_0, y_0, z_0) + t vec(x_v, y_v, z_v), forall t in RR} $
])
#note-box([L'equazione parametrica di una retta non è unica in quanto si possono considerare svariati punti diversi rispetto a $(x_0, y_0, z_0)$.])
#definition(title: [Span lineare], [
  Si dice _span lineare_ l'insieme di tutte le combinazioni lineari di un insieme di vettori.
  $ cal(L)(v_1, ..., v_k) := {w : w = a_1 v_1 + ... + a_k v_k, forall a_n in RR} $
])
#definition(title: [Piano in $AA_3$], [
  $ pi = {P : O P = vec(x, y, z) tilde.eq vec(x_0, y_0, z_0) + t vec(x_v, y_v, z_v) + s vec(x_u, y_u, z_u), v parallel.not u, forall t, s in RR} $
  dove ${v, u}$ è detta _base della giacitura del piano $pi$_. 
])

#pagebreak()
#outline(title: [Indice dei teoremi], target: figure.where(kind: "theorem"))

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
  [Fissato un punto $O$ di origine, denotiamo con $V_0^1$ l'_insieme dei vettori della retta_ con origine $O$, $V_0^2$ l'_insieme dei vettori del piano_ con origine $O$, e $V_0^3$ l'_insieme dei vettori dello spazio_ con origine $O$.],
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

#pagebreak()
#outline(title: [Indice dei teoremi], target: figure.where(kind: "theorem"))

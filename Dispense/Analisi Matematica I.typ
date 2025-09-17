#import "@preview/theorion:0.3.3": *
#import math: *

#import cosmos.rainbow: *

#show: show-theorion

= Analisi Matematica I

== Richiamo di logica

La logica si basa su *predicati* (o  *affermazioni*), i quali possono essere veri o falsi e si connettono tra loro tramite connettivi:
- *Implicazione logica* ($=>$): se l'antecedente è vero allora anche il conseguente sarà vero, ma non vale il contrario
- *Equivalenza logica* ($<=>$): la verità di uno dei due predicati implica la verità dell'altro e viceversa
- *Contrapposizione*: data un'implicazione ($p => q$) allora sarà anche vero l'implicazione di senso inverso degli opposti dei due predicati (se $p => q$, allora anche $overline(q) => overline(p)$) \ \ 

Alla base della matematica esiste il *teorema*, ossia un'implicazione logica in cui l'antecedente si dice *ipotesi* e il conseguente si dice *tesi*. La *dimostrazione* è una catena di passaggi logici che giustifica tale implicazione. Esistono tre tipi di dimostrazioni:
- *Diretta*: viene dimostrato che l'ipotesi implica la tesi
- *Indiretta per contrapposizione*: viene dimostrato che l'inverso della tesi implica l'inverso dell'ipotesi
- *Indiretta per assurdo*: viene dimostrato che la negazione della tesi porta ad un risultato falso, rendendo dunque vera la tesi
- *Per induzione*: un tipo di dimostrazione che vale solo all'interno dei numeri naturali

Esistono tre quattro diverse tipologie di teorema:
- *Lemma*: un teorema di piccola importanza
- *Proposizione*: un teorema di media importanza
- *Teorema*
- *Corollario*: l'insieme di conseguenze di un teorema

== Gli insiemi numerici

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ italic(NN) := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ italic(ZZ) := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ italic(QQ) := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$. \ \

=== I numeri razionali

Due frazioni $a/b$ e $c/d$ si dicono *equivalenti* se vale la relazione $a d = b c$. \

I numeri razionali possono anche essere rappresentati sotto forma di *allineamento decimale* (per esempio $1/2 = 0,5$). Un numero razionale può essere:
- *finito*: la parte decimale ha un numero limitato di cifre
- *periodico*: la parte decimale si ripete all'infinito con costanza

#note-box([Gli allineamenti decimali con periodo $9$ non provengono da alcuna divisione (ad esempio $0.overline(9) = 1$).])

#definition([$n in ZZ$ si dice _pari_ se $exists h in ZZ : n = 2h$ mentre si dice _dispari_ se $exists h in ZZ : n = 2h + 1$]) <raz:defpari>
#proposition(title: [Parità dei quadrati], [$n$ pari $=> n^2$ pari, $n$ dispari $=> n^2$ dispari]) <raz:pdq>
#proof([\ Sia $n in ZZ$. $n$ è pari $<=> exists h in ZZ : n = 2h$. Dunque \
  $n^2 = (2h)^2 = 4h^2 = 2(2h^2) = 2k $, essendo $k = 2h^2 in ZZ$. \
  Dunque $n^2$ è pari \ \
  Sia $n in ZZ$. $n$ è dispari $<=> exists h in ZZ : n = 2h + 1$. Dunque \
  $n^2 = (2h +1)^2 = 4h^2 + 4h + 1 = 2(2h^2 +2h) + 1 = 2k + 1$ dove $k = 2h^2 + 2h$. \
  Dunque $n^2$ è dispari
])
#proposition(title: [Parità dei quadrati parte 2], [$n^2$ pari $=> n$ pari, $n^2$ dispari $=> n$ dispari]) <raz:pdq2>
#proof([Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ])

==== Le radici

I numeri razionali presentano lacune in materia di estrazione di radici.
#definition([Sia $a >= 0$. Si dice _radice quadrata_ di $a$ un numero $b$ tale che $b^2 = a, b >= 0$.])
#theorem(title: [Irrazionalità di $sqrt(2)$], [$sqrt(2)$ non è un numero razionale.])
#proof([Supponiamo, per assurdo, che $sqrt(2) in QQ$. Dunque \
$sqrt(2) = m/n$ essendo $m,n in ZZ, n != 0, m, n$ primi tra loro. Elevando al quadrato: \
$2 = m^2/n^2 => m^2 = 2n^2$. Pertanto, per @raz:defpari, $n^2$ è pari e, per @raz:pdq2, anche $n$ è pari \
Questo è un assurdo, dal momento che $m$ e $n$ sono per definizione primi tra loro, quindi non possono essere entrambi pari.])
=== I numeri reali

L'insieme dei numeri reali rappresenta quell'insieme numerico che comprende *tutti gli allineamenti decimali finiti*,* infiniti periodici* e *infiniti non periodici*. Dunque:
$ NN subset ZZ subset QQ subset RR $

Tutti quei numeri reali che non sono razionali si dicono *numeri irrazionali*, i quali appartengono all'insieme $RR backslash QQ$.






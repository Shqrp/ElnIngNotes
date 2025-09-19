#import "@preview/theorion:0.3.3": *
#import math: *

#import cosmos.rainbow: *

#show: show-theorion

#set text(lang: "it")
#set page(header: context { if counter(page).get().at(0) != 1 { if calc.even(counter(page).get().at(0)) { align(left, [#{counter(page).display()} - _Analisi Matematica I_]) } else { align(right, [_Analisi Matematica I_ - #{counter(page).display()}])}}})
#align(center, [= Analisi Matematica I])
#align(center, [Andrea Giurgola - Prof. Fabio Punzo \ Ingegneria Elettronica, Politecnico di Milano]) \

#set heading(numbering: "1.1")
#set-theorion-numbering("1.1")
#outline(title: [Indice])
#outline(title: [Indice dei teoremi], target: figure.where(kind: "theorem"))

= Richiamo di logica

La logica si basa su *predicati* (o  *affermazioni*), i quali possono essere veri o falsi e si connettono tra loro tramite connettivi:
- *Implicazione logica* ($=>$): se l'antecedente è vero allora anche il conseguente sarà vero, ma non vale il contrario
- *Equivalenza logica* ($<=>$): la verità di uno dei due predicati implica la verità dell'altro e viceversa
- *Contrapposizione*: data un'implicazione ($p => q$) allora sarà anche vero l'implicazione di senso inverso degli opposti dei due predicati (se $p => q$, allora anche $overline(q) => overline(p)$) 

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

\ \

== Il principio di induzione

Il *principio di induzione* è un principio dimostrativo che permette di dimostrare un teorema in $NN$ riducendo notevolmente il numero di passaggi necessari. \
Sia $p(n)$ una proposizione logica che dipende dalla variabile $n in NN$. Se $p(n)$ è valida per un certo valore $n = n_0$ (*ipotesi induttiva*), allora sarà vera anche per $n_0 + 1$ (*passo induttivo*). Secondo il principio di induzione, allora $p(n)$ è vera $forall n in NN, n > n_0$. Di seguito tre esempi di teoremi dimostrabili con il principio di induzione.

#theorem(title: [Somma dei primi $n$-naturali], [
  $forall n in NN$ $sum^n_(k=1) = n/2(n+1)$
])
#proof([
  Sia $p(n)$ il suddetto teorema. \ 
  $p(0)$: $0 = 0/2(0+1), 0 = 0$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $1 + 2 + 3 + ... + n + (n + 1) = (n + 1)/2[(n + 1) + 1]$ \
  Riscrivendo la somma fino a $n$ come $p(n)$ \
  $(1 + 2 + 3 + ... + n) + (n + 1) = n/2(n + 1) + (n + 1) = (n + 1)(n/2 + 1) = (n + 1)((n + 2)/2) = (n + 1)/2(n + 1 + 1)$. In quanto si è ritornati alla scrittura di $p(n + 1)$, allora è verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, il teorema vale $forall n in NN$.
])

#theorem(title: [Disuguaglianza di Bernoulli], [
  Sia $h in RR, h > -1$. Pertanto $(1+h)^n >= 1 + n h$.
])
#proof([
  Sia $p(n)$ il suddetto teorema. \
  $p(0)$: $(1 + h)^0 >= 1 + 0, 1 >= 1$. \
  $p(n + 1)$: $(1 + h)^(n + 1) >= 1 + (n + 1)h$. Supponendo vera $p(n)$: \
  $(1 + h)^(n + 1) = (1 + h)^n (1 + h)$. Si nota che $1 + h > 0$ e che $(1 + h)^(n + 1) >= (1 + n h)$. Dunque \
  $(1 + h)^n (1 + h) >= (1 + n h)(1 + h) = n h^2 + n h + h + 1$. Dunque \
  $(1 + h)^(n + 1) >= n h^2 + n h + h + 1$. Qui $n h^2$ si può non considerare in quanto rende solo più forte la relazione di disuguaglianza. Dunque \
  $(1 + h)^(n + 1) >= n h + h + 1, (1 + h)^(n + 1) >= 1 + (n + 1)h$. \
  È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

#proposition(title: [Somma della progressione geometrica], [
  Sia $q in RR, q != 1$. $forall n in NN$ $sum^n_(k = 0)q^k = (1 - q^(n + 1))/(1 - q)$
])
#proof([
  #set par(leading: 1.25em)
  Sia $p(n)$ la suddetta proposizione. \
  $p(0)$: $q^0 = (1 - q^1)/(1 - q), 1 = cancel(1 - q)/cancel(1 - q), 1 = 1$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $sum^(n + 1)_(k = 0)q^k = (1 - q^(n + 2))/(1 - q)$
  $sum^(n + 1)_(k = 0)q^k = sum^(n)_(k = 0)q^k + q^(n + 1) = (1 - q^(n + 1))/(1 - q) + q^(n + 1) =$ \
  $= (1 - cancel(q^(n + 1)) + cancel(q^(n + 1)) - q^(n + 2))/(1 - q) = (1 - q^(n + 2))/(1 - q)$. È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

= Gli insiemi numerici

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ italic(NN) := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ italic(ZZ) := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ italic(QQ) := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$. \ \

== I numeri razionali

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
]) \ \ \ \
#proposition(title: [Parità dei quadrati parte 2], [$n^2$ pari $=> n$ pari, $n^2$ dispari $=> n$ dispari]) <raz:pdq2>
#proof([Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ])

=== Il problema delle radici

I numeri razionali presentano lacune in materia di estrazione di radici.
#definition([Sia $a >= 0$. Si dice _radice quadrata_ di $a$ un numero $b$ tale che $b^2 = a, b >= 0$.])
#theorem(title: [Irrazionalità di $sqrt(2)$], [$sqrt(2)$ non è un numero razionale.])
#proof([Supponiamo, per assurdo, che $sqrt(2) in QQ$. Dunque \
$sqrt(2) = m/n$ essendo $m,n in ZZ, n != 0, m, n$ primi tra loro. Elevando al quadrato: \
$2 = m^2/n^2 => m^2 = 2n^2$. Pertanto $m^2$ è pari e anche $m$ è pari. Dunque $exists k in Z : m = 2k$ \
$2n^2 = m^2 = (2k)^2 = 4k^2 => 2n^2 = 4k^2 => n^2 = 2k^2$. Pertanto n^2 è pari, quindi anche n è pari. \
Questo è un assurdo, dal momento che $m$ e $n$ sono per definizione primi tra loro, quindi non possono essere entrambi pari.])
== I numeri reali

L'insieme dei numeri reali rappresenta quell'insieme numerico che comprende *tutti gli allineamenti decimali finiti*,* infiniti periodici* e *infiniti non periodici*. Dunque:
$ NN subset ZZ subset QQ subset RR $

Tutti quei numeri reali che non sono razionali si dicono *numeri irrazionali*, i quali appartengono all'insieme $RR backslash QQ$.

=== La rappresentazione geometria di $RR$

Se si rappresentano i numeri razionali sulla retta, ci saranno sempre dei buchi (per es. ($sqrt(2) in RR$ ma $in.not QQ$). Invece i numeri reali, in quanto comprendono anche i non razionali, godono della *proprietà di continuità* (o *completezza*) *dei numeri reali*.

== Estremo superiore ed inferiore

Sia $E in RR$
#definition([Sia $M in RR$, si dice _massimo_ di E se $cases(M in E, M >= x\, forall x in E)$ oppure _minimo_ se $cases(M in E, M >= x\,forall x in E)$])
#example([$E = (0; 2] => max E = 2, exists.not min E$, $E = [0; 2) => exists.not max E, min E = 0$])
#definition([$Lambda in RR$ si dice _maggiorante_ di E se $Lambda >= x, forall x in E$ \ $Lambda in RR$ si dice _minorante_ di E se $Lambda >= x, forall x in E$ ])
#definition([Sia $E subset.eq RR, E != emptyset$. Si chiama _estremo superiore_ ($sup E$) di E il minimo dei maggioranti e si chiama _estremo inferiore_ ($inf E$) di E il massimo dei minoranti. ])
#example($E = (0; 2] => sup E = 2 = max E, inf E = 0$)
#note-box([Se $exists max E$ allora coincide con $sup E$])

L'estremo superiore è caratterizzato da due proprietà:
- $sup E$ è un maggiorante di E: $sup E >= x, forall x in E$
- Qualunque numero $< sup E$ non è un maggiorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon > sup E - epsilon $
L'estremo inferiore di E è caratterizzato da:
- $inf E$ è minorante di E: $inf E <= x, forall x in E$
- Qualunque numero $> inf E$ non è minorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon < inf E + epsilon$

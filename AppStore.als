module appstore

open util/ordering[Time]

-------------------------- ASSINATURAS --------------------------

sig Time {}


one sig Loja {
	aplicativos: some Aplicativo,
	usuarios: some Usuario
}

abstract sig VersaoDoApp{}
one sig Atual, Antiga extends VersaoDoApp{}

abstract sig Aplicativo {
	versao: VersaoDoApp one -> Time,
}

sig AplicativoPago extends Aplicativo{}
sig AplicativoGratis extends Aplicativo{}

sig Conta {
	cartoes : lone Cartao,
	dispositivos: some Dispositivo,
	aplicativosassociados: set Aplicativo  -> Time
}

sig Usuario{
	contas : one Conta
}

sig Dispositivo{

	apps : Status -> Aplicativo -> Time, 
}

sig Cartao {

}

abstract sig Status{}
one sig Instalado, NaoInstalado extends Status{}

-------------------------- FATOS --------------------------


fact Usuario {	
	// Todo usuario está na Loja
	all usuario: Usuario | usuario in Loja.usuarios
}

fact Loja{
	// Toda Loja tem pelo menos um Aplicativo
	all loja: Loja | some loja.aplicativos
}

fact Aplicativo {

	// Todo aplicativo no dispositivo o status é instalado e pertence a uma conta associada
	all aplicativo: Aplicativo, dispositivo: Dispositivo, status: Status, time: Time | 
	aplicativo in status.(dispositivo.apps).time => status = Instalado
	and aplicativo in dispositivo.~dispositivos.aplicativosassociados.time

	// Todo aplicativo pago tem uma conta com cartao
	all aplicativoPago: AplicativoPago,  conta: Conta, time: Time | 
	aplicativoPago in  getAplicativosAssociados[conta,time] => some conta.cartoes

	// Todo Aplicativo está na loja
	all aplicativo: Aplicativo | aplicativo in Loja.aplicativos

	// A versão de todo aplicativo que está apenas ligado a Loja é Atual
	all aplicativo: Aplicativo, conta: Conta, time: Time | !(aplicativo in   getAplicativosAssociados[conta,time]) => aplicativo.versao.time = Atual

	all aplicativo: Aplicativo, conta: Conta, time1: Time-last| let time2 = time1.next | aplicativo in  getAplicativosAssociados[conta,time1] => aplicativo in getAplicativosAssociados[conta,time2]

	
}

fact Conta{

	// Toda conta tem um usuario
	all conta: Conta | one conta.~contas

}

fact Dispositivo{

	// Todo dispositivo tem zero ou uma conta
	all d: Dispositivo |  #(d.~dispositivos) <=1

}

fact Cartao{
	// Todo cartao tem uma conta
	all c: Cartao | one c.~cartoes
}

fact traces {
	/*
	* Mudança do comportamento do modelo com o tempo
	*/
	init[first]
	all pre: Time-last| let pos = pre.next|
 	some  c: Conta, d: Dispositivo, a: Aplicativo, s: Status|
	instalaAplicativo[a,c,d,s, pre, pos] and removeAplicativo[a,c,d,s, pre, pos] and atualizaAplicativo[a,c,d,s, pre, pos] 
}

-------------------------- FUNÇÕES --------------------------

fun getAplicativosAssociados[c : Conta, t: Time] : set Aplicativo {
        c.aplicativosassociados.t & Aplicativo
}

fun getAplicativosStatus[s: Status, d: Dispositivo, time: Time] : set Aplicativo {
		 s.(d.apps).time & Aplicativo
}

fun getVersaoAplicativo[a: Aplicativo, time: Time] : one VersaoDoApp {
		a.versao.time
}

-------------------------- PREDICADOS --------------------------

pred init[t: Time]{

no (Dispositivo.apps).t
all c: Conta | no getAplicativosAssociados[c,t]

}

pred instalaAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{
	(a !in getAplicativosStatus[s, d, antes])  =>
	getAplicativosStatus[s, d, depois] = getAplicativosStatus[s, d, antes] + a
}

pred removeAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{
	(a in getAplicativosStatus[s, d, antes]) and (a in getAplicativosAssociados[c,antes]) =>
	(getAplicativosStatus[s, d, depois] = getAplicativosStatus[s, d, antes] - a) and (a in getAplicativosAssociados[c,depois])
}

pred atualizaAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{

 (a in getAplicativosStatus[s, d, antes]) and (a in  getAplicativosAssociados[c,antes]) and getVersaoAplicativo[a, antes] = Antiga => getVersaoAplicativo[a, depois] = Atual
 
}

pred novaVersaoDisponivelAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{
(a in getAplicativosStatus[s, d, depois]) and (a in  getAplicativosAssociados[c,antes]) and  getVersaoAplicativo[a, antes] = Atual => getVersaoAplicativo[a, depois] = Antiga
}
-------------------------- ASSERT'S --------------------------

assert noAppPagoSemCartao{
	// Verifica se existe aplicativo pago associado a uma conta sem cartao
	!some aplicativo: AplicativoPago, conta:Conta, time: Time
	| aplicativo in  getAplicativosAssociados[conta,time] and no conta.cartoes
}

assert noLojaSemApp {
	// Verifica se a loja tem aplicativo
	!some loja: Loja | no loja.aplicativos
}

assert noRemoveAssociacao{
	// Verifica que nenhum aplicativo vinculado a uma conta em um determinado tempo sera desvinculado depois
	!some conta : Conta, aplicativo:Aplicativo,  time1: Time-last| let time2 = time1.next | 
 aplicativo in  getAplicativosAssociados[conta,time1] and aplicativo !in  getAplicativosAssociados[conta,time2] 
}

check noRemoveAssociacao for 10
check noLojaSemApp	for 10
check noAppPagoSemCartao for 10

pred show[]{}
run show for 10 but exactly 4 Conta


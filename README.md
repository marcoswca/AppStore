# Projeto em Alloy para a disciplina de Lógica 2015.2

Nossa é equipe tem como integrantes : Gileade Kelvin, Jobson Lucas, João Victor Mafra, Rafael Albuquerque e Marcos Arruda.

Além disso, a temática do projeto é App Store(tema 2), cuja descrição é a seguinte : em uma loja online de aplicativos para celular, o usuário pode ter uma conta, e vários aplicativos associados. 
Um aplicativo associado ao usuário já foi instalado pelo menos uma vez em um dispositivo do usuário (o usuário pode ter mais de um dispositivo). O aplicativo associado, neste caso, pode ter o status de instalado ou não. 
Um aplicativo pode ter várias versões, e apenas uma destas versões está instalada em um determinado momento. Usuários podem instalar, atualizar ou remover aplicativos de seus dispositivos, no entanto não podem apagar a associação com um aplicativo.
Aplicativos podem ser pagos ou gratuitos - caso sejam pagos, o usuário só pode instalá-los se tiver um cartão de crédito válido associado à sua conta.

De maneira esquemática, a descrição do projeto em tela propõe que seja feito o seguinte :

    •    Loja precisará de todos os tipos de entidades para funcionar, já que é ela a detentora dos aplicativos os quais podem ser comprados;
  
    •    Usuário:
  
        o     Pode ter uma conta e vários aplicativos associados a ela;
     
        o     Pode ter mais de um dispositivo;
     
    •    Um Aplicativo:
    
        o     Possui Custo:
        
                -   Grátis;
                
                -   Pago – requer cartão de crédito válido associado à conta;
                
        o     Foi instalado pelo menos uma vez em um dos dispositivos;
        
        o     Possui dois status possíveis:
        
                -   Instalado;
                
                -   Não instalado;
                
        o     Possui várias versões, sendo permitido apenas uma instalada por vez;
        
        o     Não pode ter apagada sua associação com a conta de um usuário;
        
        o     Ações possíveis com um aplicativo em um dispositivo:
        
                -   Instalar;
                
                -   Atualizar;
                
                -   Remover;

# Stockfish Analyzer

Aplicativo desktop em Python para visualizar partidas PGN e analisar lances com o motor de xadrez Stockfish.

## Recursos

- Abrir ou colar partidas em formato PGN e navegar pelo tabuleiro.
- Analisar partidas com o Stockfish por profundidade ou tempo.
- Consultar variantes, posições críticas, classificação dos lances e gráfico de avaliação.
- Exportar análises para HTML e CSV.
- Usar atalhos de teclado para navegar pelos lances.

## Requisitos

- Python 3.10 ou superior.
- Stockfish instalado separadamente. Baixe uma versão compatível na [página oficial do Stockfish](https://stockfishchess.org/download/) e selecione o executável pela interface.
- Dependências Python:

```bash
python -m pip install python-chess matplotlib pillow
```

O Pillow é opcional; sem ele, o aplicativo usa caracteres para representar as peças.

## Executar

```bash
python stock.py
```

Na primeira execução, selecione o executável do Stockfish na interface. O caminho escolhido fica salvo na configuração local do usuário.

## Gerar executável no Windows

O arquivo `stock.spec` contém a configuração do PyInstaller. Com PyInstaller instalado:

```bash
python -m pip install pyinstaller
pyinstaller stock.spec
```

O executável gerado fica em `dist/`, que não é versionada.

## Créditos e licenças

Este projeto utiliza [python-chess](https://python-chess.readthedocs.io/) e o motor [Stockfish](https://stockfishchess.org/), que é distribuído sob a GNU General Public License versão 3. O Stockfish não está incluído neste repositório; consulte a licença e os avisos na distribuição oficial que você baixar. As imagens das peças são baseadas no conjunto Cburnett, de Colin M. L. Burnett, sob CC BY-SA 3.0.

## Portfólio

Projeto desenvolvido para demonstrar uma interface desktop em Python, integração com um motor UCI, visualização de dados e exportação de relatórios. Sugestões e contribuições são bem-vindas.

FROM cimg/python:3.8

RUN wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O /tmp/packages-microsoft-prod.deb
RUN sudo dpkg -i /tmp/packages-microsoft-prod.deb
RUN sudo apt-get update && sudo apt-get install -y apt-transport-https
RUN sudo apt-get update && sudo apt-get install -y dotnet-sdk-3.1
RUN dotnet tool install -g Microsoft.Quantum.IQSharp
USER circleci
RUN pip install jupyter
RUN export PATH=$HOME/.dotnet/tools:$PATH && dotnet iqsharp install --user

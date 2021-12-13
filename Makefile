GIT_TAG:=$(shell git log -1 --pretty=%H)
DATE_TAG:=$(shell date +%Y%m%d-%H%M)

cimg_python_qsharp:
	export DOCKER_BUILDKIT=1 && docker build . --build-arg GIT_HASH=$(GIT_TAG) --build-arg BUILD_DATE=$(DATE_TAG) -t cimg_python_qsharp
	docker tag cimg_python_qsharp:latest $(GIT_TAG)
	docker tag cimg_python_qsharp:latest $(DATE_TAG)

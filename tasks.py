from invoke import task, Collection

# pty=True added so that the tasks understand they're being run in a terminal
# and keep their pretty colored output
@task
def watch_for_mypy(c):
    c.run(
        "watchmedo shell-command --drop --command='mypy tests qcware_transpile' --recursive tests qcware_transpile",
        pty=True
    )


@task
def watch_for_tests(c):
    c.run(
        "watchmedo shell-command --drop --command='pytest -v tests' --recursive tests qcware_transpile",
        pty=True
    )


watches = Collection("watch")
watches.add_task(watch_for_mypy, "mypy")
watches.add_task(watch_for_tests, "tests")

ns = Collection()
ns.add_collection(watches, "watch")

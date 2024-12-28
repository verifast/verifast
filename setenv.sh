WORKSPACEFOLDER="`cd $(dirname "${BASH_SOURCE[0]}") && pwd`"
if [[ -z "$VFDEPS_NAME" ]]; then
    . "$WORKSPACEFOLDER/config.sh"
fi
case ":${PATH}:" in
    *:"/tmp/$VFDEPS_NAME/bin":*)
        ;;
    *)
        export PATH="/tmp/$VFDEPS_NAME/bin:$PATH"
        ;;
esac
case ":$WORKSPACEFOLDER/bin:" in
    *:"/$WORKSPACEFOLDER/bin":*)
        ;;
    *)
        export PATH="$WORKSPACEFOLDER/bin:$PATH"
        ;;
esac
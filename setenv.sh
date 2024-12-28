if [[ -z "$VFDEPS_NAME" ]]; then
    . `dirname "$0"`/config.sh
fi
case ":${PATH}:" in
    *:"/tmp/$VFDEPS_NAME/bin":*)
        ;;
    *)
        export PATH="/tmp/$VFDEPS_NAME/bin:$PATH"
        ;;
esac